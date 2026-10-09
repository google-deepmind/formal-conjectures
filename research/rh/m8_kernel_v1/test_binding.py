"""Mutation tests for original-definition rebinding, independent of Lean execution."""
from pathlib import Path
import contextlib
import os
import tempfile
import unittest
import bind_pr52 as b

@contextlib.contextmanager
def isolated():
    cwd=Path.cwd()
    with tempfile.TemporaryDirectory() as d:
        os.chdir(d)
        Path('research/rh/m8_kernel_v1').mkdir(parents=True)
        try: yield
        finally: os.chdir(cwd)

class BindingTests(unittest.TestCase):
    def test_adapter_accepts_only_original_import(self):
        with isolated():
            p=Path('research/rh/m8_kernel_v1/CorrectionSymbolAdapter.lean')
            p.write_bytes(b.ADAPTER_BYTES)
            self.assertEqual(b.ReboundBuilder().origin(b.ADAPTER),p)
            p.write_bytes(b.ADAPTER_BYTES+b'axiom wrong : False\n')
            with self.assertRaises(ValueError): b.ReboundBuilder().origin(b.ADAPTER)
    def test_adapter_rejects_other_source(self):
        with isolated():
            p=Path('research/rh/m8_kernel_v1/CorrectionSymbolAdapter.lean')
            p.write_text('import AEGISOverlay.RHKreinCorrectionSymbolV1\n')
            with self.assertRaises(ValueError): b.ReboundBuilder().origin(b.ADAPTER)
    def test_producer_pin_accepts_artifact_copy(self):
        p=Path(__file__).with_name('RHKreinCorrectionM8BoundV1.lean')
        self.assertEqual(b.r.blob(p.read_bytes()),b.PRODUCER_BLOB)
    def test_producer_rejects_change(self):
        with isolated():
            p=Path('research/rh/m8_kernel_v1/RHKreinCorrectionM8BoundV1.lean')
            p.write_text('-- changed producer\n')
            with self.assertRaises(ValueError): b.ReboundBuilder().origin(b.PRODUCER)
    def test_upstream_missing_fails_closed(self):
        with isolated():
            with self.assertRaises(ValueError): b.ReboundBuilder().origin('AEGISOverlay.Missing')

if __name__=='__main__':unittest.main()
