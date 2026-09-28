#!/usr/bin/env python3
"""Tests for the Verso HTML post-processing step."""

import os
import tempfile
import unittest
from urllib.parse import parse_qs, urljoin, urlsplit

import fix_literate_html as fix


class BreadcrumbTest(unittest.TestCase):

    def test_parent_links_resolve_to_filtered_modules_under_any_base_path(self):
        html = '''<ol class="breadcrumbs" aria-label="Breadcrumb">
<li><a href="FormalConjectures/">FormalConjectures</a></li>
<li><a href="FormalConjectures/Wikipedia/">Wikipedia</a></li>
<li><span class="current">ABC</span></li></ol>'''
        fixed = fix.fix_breadcrumbs(html)
        for base in ('https://example.com/', 'https://example.com/formal-conjectures/'):
            page = urljoin(base, 'src/FormalConjectures/Wikipedia/ABC/')
            verso_base = urljoin(page, '../../../')
            for prefix in ('FormalConjectures.', 'FormalConjectures.Wikipedia.'):
                href = '../modules/?q=' + prefix
                self.assertIn(f'href="{href}"', fixed)
                target = urlsplit(urljoin(verso_base, href))
                self.assertEqual(target.path, urlsplit(urljoin(base, 'modules/')).path)
                self.assertEqual(parse_qs(target.query), {'q': [prefix]})
        self.assertIn('<span class="current">ABC</span>', fixed)
        self.assertEqual(fix.fix_breadcrumbs(fixed), fixed)

    def test_nested_escaped_names_and_non_breadcrumb_links(self):
        link = '<a href="FormalConjectures/Arxiv/%C2%AB0911.2077%C2%BB/">Paper</a>'
        html = f'<nav>{link}</nav><ol class="breadcrumbs"><li>{link}</li></ol>'
        fixed = fix.fix_breadcrumbs(html)
        self.assertIn(f'<nav>{link}</nav>', fixed)
        self.assertIn(
            'href="../modules/?q=FormalConjectures.Arxiv.%C2%AB0911.2077%C2%BB."',
            fixed,
        )


class FixHtmlFileTest(unittest.TestCase):

    def test_injects_theme_and_katex_once(self):
        with tempfile.TemporaryDirectory() as directory:
            page = os.path.join(directory, 'index.html')
            with open(page, 'w', encoding='utf-8') as f:
                f.write('<html><head><base href="../"></head><body>Lean</body></html>')

            self.assertTrue(fix.fix_html_file(page))
            self.assertFalse(fix.fix_html_file(page))

            with open(page, encoding='utf-8') as f:
                html = f.read()
            self.assertEqual(html.count('href="lean-syntax.css"'), 1)
            self.assertEqual(html.count('katex.min.css'), 1)
            self.assertEqual(html.count('renderMathInElement(document.body'), 1)

    def test_preserves_code_and_links(self):
        with tempfile.TemporaryDirectory() as directory:
            page = os.path.join(directory, 'index.html')
            body = '<body><code class="hl lean block"><a class="token const" href="#x">x</a></code></body>'
            with open(page, 'w', encoding='utf-8') as f:
                f.write(
                    '<html><head><link href="katex.min.css">'
                    '</head>' + body + '</html>'
                )
            self.assertTrue(fix.fix_html_file(page))
            self.assertFalse(fix.fix_html_file(page))
            with open(page, encoding='utf-8') as f:
                html = f.read()
            self.assertIn(body, html)
            self.assertEqual(html.count('href="lean-syntax.css"'), 1)

    def test_existing_katex_does_not_prevent_theme_injection(self):
        with tempfile.TemporaryDirectory() as directory:
            page = os.path.join(directory, 'index.html')
            with open(page, 'w', encoding='utf-8') as f:
                f.write(
                    '<html><head><link href="katex.min.css"></head>'
                    '<body><script>renderMathInElement(document.body)</script></body></html>'
                )

            self.assertTrue(fix.fix_html_file(page))

            with open(page, encoding='utf-8') as f:
                html = f.read()
            self.assertEqual(html.count('href="lean-syntax.css"'), 1)
            self.assertEqual(html.count('katex.min.css'), 1)
            self.assertEqual(html.count('renderMathInElement(document.body'), 1)


class InstallStylesheetTest(unittest.TestCase):

    def test_installs_the_shared_theme_at_the_literate_root(self):
        with tempfile.TemporaryDirectory() as directory:
            fix.install_highlight_stylesheet(directory)
            installed = os.path.join(directory, fix.HIGHLIGHT_STYLESHEET)

            with open(fix.HIGHLIGHT_STYLESHEET_SOURCE, encoding='utf-8') as f:
                source_css = f.read()
            with open(installed, encoding='utf-8') as f:
                installed_css = f.read()
            self.assertEqual(installed_css, source_css)


if __name__ == '__main__':
    unittest.main()
