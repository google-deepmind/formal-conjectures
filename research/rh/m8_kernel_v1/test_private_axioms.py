"""Lean's printed private-name prefix must be bound to the current source module."""
import unittest
import replay as r

SOURCE='namespace N\nprivate theorem f : True := by trivial\nend N\n#print axioms N.f\n'
PRIVATE="'_private.Example.0.N.f' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
class PrivateAxiomTests(unittest.TestCase):
    def test_valid_private_probe(self):
        self.assertEqual(r.audit(SOURCE,PRIVATE,module_name='Example'),1)
    def test_wrong_module_rejected(self):
        with self.assertRaises(ValueError):r.audit(SOURCE,PRIVATE,module_name='Different')
    def test_public_source_rejects_private_substitution(self):
        with self.assertRaises(ValueError):r.audit(SOURCE.replace('private ',''),PRIVATE,module_name='Example')
    def test_private_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):r.audit(SOURCE,PRIVATE.replace('Quot.sound','sorryAx'),module_name='Example')
    def test_duplicate_public_private_rejected(self):
        with self.assertRaises(ValueError):r.audit(SOURCE,PRIVATE+"'N.f' depends on axioms: []\n",module_name='Example')
    def test_no_module_context_rejects_private(self):
        with self.assertRaises(ValueError):r.audit(SOURCE,PRIVATE)
if __name__=='__main__':unittest.main()
