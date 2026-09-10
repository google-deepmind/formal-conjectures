"""Retain Verso output without fetching a corpus-wide hover database in the browser."""
from pathlib import Path
import tempfile
import unittest
import extract_verso_fragments as extract


class FragmentTest(unittest.TestCase):
    def test_defining_site_retains_its_code_docstring_and_only_referenced_hovers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            page = root / 'FormalConjectures' / 'Example' / 'index.html'
            page.parent.mkdir(parents=True)
            page.write_text('''<html><head><title>FormalConjectures.Example</title></head>
<body><div class="mod-doc">Module source</div><div class="md-text">First statement</div>
<code class="hl lean block"><span id="first" data-binding="const-Example.first">first</span>
<span data-verso-hover="used">Nat</span></code>
<div class="md-text">Second statement</div>
<code class="hl lean block"><span id="second" data-binding="const-Example.second">second</span>
<span data-binding="const-Example.first">use of first</span></code></body></html>''')
            module_path, name, doc, links = extract.extract_from_html(
                page, root, {'used':'<b>Nat</b>', 'unrelated':'Unrelated hover'})
            self.assertEqual(name, 'FormalConjectures.Example')
            self.assertEqual(module_path, '/FormalConjectures/Example/')
            self.assertEqual(doc, 'Module source')
            self.assertEqual(set(links), {'Example.first', 'Example.second'})
            self.assertEqual(links['Example.first']['docHtml'], 'First statement')
            self.assertEqual(links['Example.second']['docHtml'], 'Second statement')
            self.assertEqual(links['Example.first']['hoverDocs'], {'used':'<b>Nat</b>'})
            self.assertEqual(links['Example.second']['hoverDocs'], {})
            self.assertIn('id="first"', links['Example.first']['codeHtml'])
            self.assertNotIn('id="second"', links['Example.first']['codeHtml'])
