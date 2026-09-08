#!/usr/bin/env python3
"""Tests for the Verso HTML post-processing step."""

import os
import tempfile
import unittest

import fix_literate_html as fix


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

    def test_removes_old_highlighter_without_changing_code(self):
        with tempfile.TemporaryDirectory() as directory:
            page = os.path.join(directory, 'index.html')
            body = '<body><code class="hl lean block"><a class="token const" href="#x">x</a></code></body>'
            with open(page, 'w', encoding='utf-8') as f:
                f.write(
                    '<html><head><link href="katex.min.css">'
                    '<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/highlight.js@11.12.0/styles/atom-one-light.min.css">'
                    '<link rel="stylesheet" href="lean-highlight.css">'
                    '<script defer src="lean-highlight.js"></script>'
                    '</head>' + body + '</html>'
                )
            self.assertTrue(fix.fix_html_file(page))
            self.assertFalse(fix.fix_html_file(page))
            with open(page, encoding='utf-8') as f:
                html = f.read()
            self.assertNotIn('lean-highlight', html)
            self.assertNotIn('highlight.js', html)
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
            for filename in ('lean-highlight.js', 'lean-highlight.css'):
                with open(os.path.join(directory, filename), 'w') as f:
                    f.write('obsolete')
            fix.install_highlight_stylesheet(directory)
            for filename in ('lean-highlight.js', 'lean-highlight.css'):
                self.assertFalse(os.path.exists(os.path.join(directory, filename)))
            installed = os.path.join(directory, fix.HIGHLIGHT_STYLESHEET)

            with open(fix.HIGHLIGHT_STYLESHEET_SOURCE, encoding='utf-8') as f:
                source_css = f.read()
            with open(installed, encoding='utf-8') as f:
                installed_css = f.read()
            self.assertEqual(installed_css, source_css)


if __name__ == '__main__':
    unittest.main()
