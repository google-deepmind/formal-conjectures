#!/usr/bin/env python3
"""
Post-process Verso literate HTML output to fix deployment issues.

Fixes:
1. Adds KaTeX for LaTeX rendering in docstrings
2. Creates stub JS files for missing search infrastructure
3. Fixes domain-mappers.js module syntax
4. Installs the Formal Conjectures Lean syntax-highlighting theme
5. Installs the source-page layout script

Usage: python3 fix_literate_html.py <literate-html-dir>
"""

import os
import shutil
import sys


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
HIGHLIGHT_STYLESHEET = 'lean-syntax.css'
HIGHLIGHT_STYLESHEET_SOURCE = os.path.join(
    SCRIPT_DIR, 'src', 'css', HIGHLIGHT_STYLESHEET
)
SOURCE_PAGE_SCRIPT = 'source-page.js'
SOURCE_PAGE_SCRIPT_SOURCE = os.path.join(
    SCRIPT_DIR, 'src', 'js', SOURCE_PAGE_SCRIPT
)

HIGHLIGHT_HEAD = f'''
    <!-- Formal Conjectures Lean syntax-highlighting theme -->
    <link rel="stylesheet" href="{HIGHLIGHT_STYLESHEET}">
'''

SOURCE_PAGE_HEAD = f'''
    <!-- Formal Conjectures source-page layout -->
    <script defer src="{SOURCE_PAGE_SCRIPT}"></script>
'''

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


def fix_html_file(path):
    """Inject KaTeX and the Lean syntax theme into a Verso HTML file."""
    with open(path, 'r', encoding='utf-8') as f:
        html = f.read()

    modified = False

    head_additions = ''
    if HIGHLIGHT_STYLESHEET not in html:
        head_additions += HIGHLIGHT_HEAD
    if SOURCE_PAGE_SCRIPT not in html:
        head_additions += SOURCE_PAGE_HEAD
    if 'katex' not in html.lower():
        head_additions += KATEX_HEAD

    # Add styles and scripts before </head>. Pages contain a <base> element,
    # so the relative theme URL resolves to the root of the literate output.
    if head_additions and '</head>' in html:
        html = html.replace('</head>', head_additions + '  </head>', 1)
        modified = True

    # Add auto-render script before </body>
    if 'renderMathInElement(document.body' not in html and '</body>' in html:
        html = html.replace('</body>', KATEX_BODY_SCRIPT + '</body>', 1)
        modified = True

    if modified:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(html)
    return modified


def install_highlight_stylesheet(literate_dir):
    """Copy the self-hosted Lean syntax theme into the Verso output root."""
    destination = os.path.join(literate_dir, HIGHLIGHT_STYLESHEET)
    shutil.copyfile(HIGHLIGHT_STYLESHEET_SOURCE, destination)
    print(f'  Installed syntax theme: {HIGHLIGHT_STYLESHEET}')


def install_source_page_script(literate_dir):
    """Copy the source-page layout script into the Verso output root."""
    destination = os.path.join(literate_dir, SOURCE_PAGE_SCRIPT)
    shutil.copyfile(SOURCE_PAGE_SCRIPT_SOURCE, destination)
    print(f'  Installed source-page layout: {SOURCE_PAGE_SCRIPT}')


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


def main():
    if len(sys.argv) < 2:
        print('Usage: python3 fix_literate_html.py <literate-html-dir>', file=sys.stderr)
        sys.exit(1)

    literate_dir = sys.argv[1]
    if not os.path.isdir(literate_dir):
        print(f'  Warning: {literate_dir} not found, skipping.', file=sys.stderr)
        return

    install_highlight_stylesheet(literate_dir)
    install_source_page_script(literate_dir)

    # Create stubs for missing JS files
    create_stubs(literate_dir)

    # Fix all HTML files
    count = 0
    for dirpath, _, filenames in os.walk(literate_dir):
        for f in filenames:
            if f == 'index.html':
                path = os.path.join(dirpath, f)
                if fix_html_file(path):
                    count += 1

    print(f'  Post-processed {count} Verso HTML files.')


if __name__ == '__main__':
    main()
