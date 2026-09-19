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

    def test_snapshot_check_rejects_dirty_root_aggregates_and_lake_configuration(self):
        import contextlib
        import io
        import subprocess
        import sys
        from unittest.mock import patch
        sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
        import publish_catalog

        with tempfile.TemporaryDirectory(prefix='fc-verso-source-') as directory:
            root = Path(directory)
            def git(*args):
                subprocess.run(['git', '-C', directory, *args], check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            git('init'); git('config', 'user.name', 'Fixture'); git('config', 'user.email', 'fixture@example.invalid')
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
            (root/'lake-manifest.json').write_text('{}')
            inputs = ('FormalConjecturesUtil.lean', 'FormalConjecturesForMathlib.lean', 'lakefile.toml')
            for name in inputs:
                (root/name).write_text('')
            git('add', '.'); git('commit', '-m', 'Pinned inputs')
            data = {'schemaVersion': 2, 'problems': [{'theorem': 'Example.self',
                'module': 'FormalConjectures.Example', 'category': 'test', 'subjects': ['11'],
                'statement': 'True', 'docstring': 'Fixture', 'answerKinds': [], 'hasSorryFreeProof': False}],
                'moduleDocstrings': {'FormalConjectures.Example': 'Source'}}
            catalog = root/'catalog'
            publish_catalog.prepare(root, 'owner/fc', data, catalog)
            html = root/'html'; html.mkdir()
            (html/'index.html').write_text('<title>FormalConjectures.Example</title>')
            output = root/'rendering.json'
            with patch.object(extract, '__file__', str(root/'site/extract_verso_fragments.py')), \
                 patch.object(sys, 'argv', ['extract', str(html), str(output), '--catalog-dir', str(catalog)]):
                for name in inputs:
                    for state in ('modified', 'staged', 'deleted'):
                        with self.subTest(file=name, state=state):
                            if state=='deleted': (root/name).unlink()
                            else: (root/name).write_text('changed\n')
                            if state=='staged': git('add', name)
                            error = io.StringIO()
                            with contextlib.redirect_stderr(error), self.assertRaises(SystemExit) as raised:
                                extract.main()
                            self.assertEqual(raised.exception.code, 2)
                            self.assertIn('source and dependency inputs must be committed', error.getvalue())
                            self.assertFalse(output.exists())
                            git('restore', '--source=HEAD', '--staged', '--worktree', '--', name)
                with contextlib.redirect_stdout(io.StringIO()):
                    extract.main()
                self.assertTrue(output.is_file())
