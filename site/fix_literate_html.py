#!/usr/bin/env python3
"""
Post-process Verso literate HTML output to fix deployment issues.

Fixes:
1. Adds KaTeX for LaTeX rendering in docstrings
2. Creates stub JS files for missing search infrastructure
3. Fixes domain-mappers.js module syntax
4. Installs the shared Verso syntax theme
5. Adds a root index page that redirects to the website's module index
6. Links parent breadcrumbs to the filtered module index

Usage: python3 fix_literate_html.py <literate-html-dir>
"""

import os
import re
import shutil
import sys
from html import escape, unescape
from urllib.parse import quote, unquote

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
HIGHLIGHT_STYLESHEET = 'lean-syntax.css'
HIGHLIGHT_STYLESHEET_SOURCE = os.path.join(SCRIPT_DIR, 'src', 'css', HIGHLIGHT_STYLESHEET)
HIGHLIGHT_HEAD = f'<link rel="stylesheet" href="{HIGHLIGHT_STYLESHEET}">\n'

KATEX_HEAD = '''
    <!-- KaTeX for LaTeX in docstrings -->
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.21/dist/katex.min.css" crossorigin="anonymous">
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.21/dist/katex.min.js" crossorigin="anonymous"></script>
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.21/dist/contrib/auto-render.min.js" crossorigin="anonymous"></script>
'''

KATEX_BODY_SCRIPT = '''
<script>
document.addEventListener("DOMContentLoaded", function() {
  if (typeof renderMathInElement === 'function') {
    renderMathInElement(document.body, {
      delimiters: [
        {left: '$$', right: '$$', display: true},
        {left: '$', right: '$', display: false},
      ],
      throwOnError: false
    });
  }
});
</script>
'''


def fix_breadcrumbs(html):
    """Point Verso's parent-folder links to the website's module index."""
    def fix_list(match):
        def fix_link(link):
            href = unescape(link.group(1))
            if not href.endswith('/') or href.startswith(('../', '/', '#')) or ':' in href:
                return link.group(0)
            # The trailing dot keeps similarly named libraries out of the results.
            prefix = unquote(href).replace('/', '.')
            target = '../modules/?q=' + quote(prefix, safe='')
            return f'href="{escape(target, quote=True)}"'

        return re.sub(r'href="([^"]*)"', fix_link, match.group(0))

    # Limit rewriting to navigation; source-code and sidebar links stay intact.
    return re.sub(r'<ol\b[^>]*class="breadcrumbs"[^>]*>.*?</ol>',
                  fix_list, html, flags=re.DOTALL)


def fix_html_file(path):
    """Install the syntax theme and KaTeX in a Verso HTML file."""
    with open(path, 'r', encoding='utf-8') as f:
        html = f.read()

    fixed_html = fix_breadcrumbs(html)
    modified = fixed_html != html
    html = fixed_html

    # Add these independently: cached pages may already contain KaTeX.
    if f'href="{HIGHLIGHT_STYLESHEET}"' not in html and '</head>' in html:
        html = html.replace('</head>', HIGHLIGHT_HEAD + '  </head>')
        modified = True

    # Add KaTeX CSS+JS before </head>
    if 'katex' not in html.lower() and '</head>' in html:
        html = html.replace('</head>', KATEX_HEAD + '  </head>')
        if '</body>' in html:
            html = html.replace('</body>', KATEX_BODY_SCRIPT + '</body>')
        modified = True

    if modified:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(html)
    return modified


def install_highlight_stylesheet(literate_dir):
    """Install the shared Verso theme."""
    shutil.copyfile(HIGHLIGHT_STYLESHEET_SOURCE,
                    os.path.join(literate_dir, HIGHLIGHT_STYLESHEET))


def create_stubs(literate_dir):
    """Create stub files for missing Verso search infrastructure."""
    search_dir = os.path.join(literate_dir, '-verso-search')
    os.makedirs(search_dir, exist_ok=True)

    stubs = {
        'searchIndex.js': '// Stub: search index not available for literate pages\n',
        'search-init.js': '// Stub: search not available for literate pages\n',
        'elasticlunr.min.js': '// Stub\n',
    }
    for name, content in stubs.items():
        path = os.path.join(search_dir, name)
        if not os.path.exists(path):
            with open(path, 'w') as f:
                f.write(content)
            print(f'  Created stub: -verso-search/{name}')

    # Fix domain-mappers.js: remove export statements that cause syntax errors
    # when loaded without type="module"
    dm_path = os.path.join(search_dir, 'domain-mappers.js')
    if os.path.exists(dm_path):
        with open(dm_path, 'r') as f:
            content = f.read()
        if 'export ' in content:
            # Wrap in IIFE and remove exports
            fixed = content.replace('export ', '')
            with open(dm_path, 'w') as f:
                f.write(fixed)
            print('  Fixed domain-mappers.js (removed export statements)')


# `verso-html` writes one page per module but no landing page, so the root of
# the literate output is a 404. The website has a module index of its own, one
# directory up from where this tree is deployed (`/src/` next to `/modules/`),
# and this page sends the visitor there. The link is relative so that it works
# under any base path.
ROOT_REDIRECT_HTML = '''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta http-equiv="refresh" content="0; url=../modules/">
  <link rel="canonical" href="../modules/">
  <title>Redirecting to the module index</title>
</head>
<body>
  <p>The annotated source pages are listed on the <a href="../modules/">module index</a>.</p>
</body>
</html>
'''


def create_root_index(literate_dir):
    """Write a redirect page at the root unless Verso already produced one."""
    path = os.path.join(literate_dir, 'index.html')
    if os.path.exists(path):
        return
    with open(path, 'w', encoding='utf-8') as f:
        f.write(ROOT_REDIRECT_HTML)
    print('  Created root index.html (redirect to /modules/)')


def fix_code_css(literate_dir):
    """Fix layout and scrolling issues in code.css."""
    css_path = os.path.join(literate_dir, 'code.css')
    if not os.path.exists(css_path):
        return

    with open(css_path, 'r', encoding='utf-8') as f:
        content = f.read()

    modified = False
    if '.content-wrapper' not in content:
        content += '''
/* Content wrapper: flex row for code content + page ToC */
.content-wrapper {
    flex: 1;
    display: flex;
    flex-direction: row;
    overflow: hidden;
    min-height: 0;
}

.main-area {
    min-height: 0;
}

.code-content {
    min-height: 0;
}
'''
        modified = True

    if modified:
        with open(css_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print('  Fixed code.css (added .content-wrapper layout rules)')


def main():
    if len(sys.argv) < 2:
        print('Usage: python3 fix_literate_html.py <literate-html-dir>', file=sys.stderr)
        sys.exit(1)

    literate_dir = sys.argv[1]
    if not os.path.isdir(literate_dir):
        print(f'  Warning: {literate_dir} not found, skipping.', file=sys.stderr)
        return

    # Create stubs for missing JS files
    create_stubs(literate_dir)

    # Fix code.css layout rules
    fix_code_css(literate_dir)

    # Verso's <base> points to this root even on deeply nested source pages.
    install_highlight_stylesheet(literate_dir)

    # Fix all HTML files
    count = 0
    for dirpath, _, filenames in os.walk(literate_dir):
        for f in filenames:
            if f == 'index.html':
                path = os.path.join(dirpath, f)
                if fix_html_file(path):
                    count += 1

    print(f'  Updated rendering assets in {count} Verso HTML files.')

    # Written last so that the redirect page is not treated as a module page.
    create_root_index(literate_dir)


if __name__ == '__main__':
    main()
