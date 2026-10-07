# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from verify_rh_compile_graph_v1 import audit, compile_plan

WORKFLOW = '''- name: Compile and audit certified approximation and spectral obstruction
    run: |
      for m in First; do
        true
      done
      for m in Second Third; do
        true
      done
- name: Upload Krein bridge replay logs
'''

class CompileGraphTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'AEGISOverlay').mkdir()
        self.write('First', 'import Mathlib.Tactic')
        self.write('Second', 'import AEGISOverlay.First')
        self.write('Third', 'import Second')

    def write(self, name, text):
        (self.root / 'AEGISOverlay' / f'{name}.lean').write_text(text)

    def test_passes_valid_import_graph(self):
        self.assertEqual(audit(self.root, WORKFLOW), ([], 2))

    def test_rejects_wrong_root_prefix(self):
        self.write('Second', 'import First')
        self.assertIn('expects AEGISOverlay', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_wrong_overlay_prefix(self):
        self.write('Third', 'import AEGISOverlay.Second')
        self.assertIn('expects root', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_reverse_order(self):
        self.write('Second', 'import Third')
        self.assertIn('built after', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_omitted_source(self):
        self.write('Second', 'import AEGISOverlay.Omitted')
        self.write('Omitted', 'import Mathlib.Tactic')
        self.assertIn('omitted', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_unresolved_overlay(self):
        self.write('Second', 'import AEGISOverlay.Missing')
        self.assertIn('unresolved', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_duplicate_modules(self):
        w = WORKFLOW.replace('for m in Second Third', 'for m in First Third')
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            compile_plan(w)

    def test_rejects_missing_source(self):
        (self.root / 'AEGISOverlay' / 'Third.lean').unlink()
        self.assertIn('missing declared source', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_accepts_only_proven_prebuilt_root(self):
        self.write('Second', 'import RHKreinCriticalLineBridgeV1')
        self.write('RHKreinCriticalLineBridgeV1', 'import Mathlib.Tactic')
        earlier = ("- name: Compile critical-line Mellin Fourier bridge\n"
                   "    run: |\n"
                   "      cp AEGISOverlay/RHKreinCriticalLineBridgeV1.lean RHKreinCriticalLineBridgeV1.lean\n"
                   "      lake env lean -o .lake/build/lib/lean/RHKreinCriticalLineBridgeV1.olean RHKreinCriticalLineBridgeV1.lean\n")
        self.assertEqual(audit(self.root, earlier + WORKFLOW), ([], 2))

    def test_rejects_unverified_prebuilt_root(self):
        self.write('Second', 'import RHKreinCriticalLineBridgeV1')
        self.write('RHKreinCriticalLineBridgeV1', 'import Mathlib.Tactic')
        self.assertIn('omitted', '\n'.join(audit(self.root, WORKFLOW)[0]))

    def test_rejects_unrecognized_plan(self):
        with self.assertRaisesRegex(ValueError, 'compile-step anchors'):
            compile_plan('unrelated workflow')

if __name__ == '__main__':
    unittest.main()
