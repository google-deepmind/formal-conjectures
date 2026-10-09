import importlib.util
from pathlib import Path
import unittest

class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).with_name('replay.py')
        cls.path = path
        if path.exists():
            spec = importlib.util.spec_from_file_location('replay', path)
            cls.m = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(cls.m)
        else:
            cls.m = None
    def test_implementation_exists(self):
        self.assertIsNotNone(self.m, 'new replay verifier is absent')
    def check_module(self):
        if self.m is None: self.skipTest('red baseline: implementation absent')
    def test_imports_strip_comments_and_strings(self):
        self.check_module()
        text = '/- import Bad\n /- nested -/ -/\npublic import Mathlib.A\nimport Foo.Bar Baz -- no\ndef s := "import NotReal"\n'
        self.assertEqual(self.m.imports(text), ['Mathlib.A', 'Foo.Bar', 'Baz'])
    def test_git_blob(self):
        self.check_module()
        self.assertEqual(self.m.blob(b''), 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391')
    def test_accept_standard(self):
        self.check_module()
        self.assertEqual(self.m.audit('#print axioms X\n', "'X' depends on axioms: [propext, Classical.choice, Quot.sound]\n"), 1)
    def test_accept_no_axioms(self):
        self.check_module()
        self.assertEqual(self.m.audit('#print axioms X\n', "'X' does not depend on any axioms\n"), 1)
    def test_reject_bad_audits(self):
        self.check_module()
        for text in ['', "'X' depends on axioms: [sorryAx]", "'X' depends on axioms: [custom]", "error: no\n'X' depends on axioms: []", "'X' depends on axioms: []\n'X' depends on axioms: []", "'Y' depends on axioms: []"]:
            with self.subTest(text=text), self.assertRaises(ValueError): self.m.audit('#print axioms X\n', text)
    def test_reject_repeated_source_probe(self):
        self.check_module()
        with self.assertRaises(ValueError): self.m.audit('#print axioms X\n#print axioms X\n', "'X' depends on axioms: []")
    def test_pinned_patch(self):
        self.check_module()
        p=Path('/mnt/data/rh_m8_kernel_cycle/baseline_packet/sources/RHKreinExplicitCorrectionV1.lean')
        if not p.exists(): p=Path('.baseline/AEGISOverlay/RHKreinExplicitCorrectionV1.lean')
        self.assertTrue(p.exists(), 'exact baseline fixture is required')
        patched=self.m.patched_correction(p.read_bytes())
        self.assertEqual(self.m.blob(patched), self.m.PATCHED_BLOB)
        with self.assertRaises(ValueError): self.m.patched_correction(p.read_bytes()+b'\n')
    def test_extract_shell(self):
        self.check_module()
        s='      - name: Check\n        run: |\n          echo hi\n          echo bye\n      - name: Other\n'
        self.assertEqual(self.m.shell_block(s,'Check'), 'echo hi\necho bye\n')
        with self.assertRaises(ValueError): self.m.shell_block(s,'Missing')
if __name__=='__main__': unittest.main()
