"""Exact active-namespace resolution, including the PR53 hosted failure."""
import unittest
import replay as r

MODULE = 'WeilThreeBlockTranslatedPacketsV22'
NAMESPACE = 'AEGIS.' + MODULE
SOURCE = 'noncomputable section\nnamespace ' + NAMESPACE + '\n#print axioms logLift_translate\nend ' + NAMESPACE + '\n'
LOG = "'" + NAMESPACE + ".logLift_translate' depends on axioms: [propext, Classical.choice, Quot.sound]\n"

class NamespaceAxiomTests(unittest.TestCase):
    def test_hosted_namespace_result(self):
        self.assertEqual(r.audit(SOURCE, LOG, module_name=MODULE), 1)

    def test_reject_other_namespace_and_suffix(self):
        for namespace in ['Other.' + MODULE, NAMESPACE + '.Nested', 'Prefix.' + NAMESPACE]:
            with self.subTest(namespace=namespace), self.assertRaises(ValueError):
                r.audit(SOURCE, LOG.replace(NAMESPACE, namespace), module_name=MODULE)

    def test_reject_duplicate_or_ambiguous_results(self):
        for extra in [LOG, "'logLift_translate' depends on axioms: []\n",
                      "'" + NAMESPACE + ".logLift_translate' does not depend on any axioms\n"]:
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                r.audit(SOURCE, LOG + extra, module_name=MODULE)

    def test_nested_scopes_and_closed_namespace(self):
        source = 'namespace A\nnamespace B\nsection S\n#print axioms f\nend S\nend B\n#print axioms g\nend A\n#print axioms h\n'
        log = "'A.B.f' depends on axioms: []\n'A.g' depends on axioms: []\n'h' does not depend on any axioms\n"
        self.assertEqual(r.audit(source, log, module_name='Example'), 3)

    def test_comments_and_strings_do_not_change_scope(self):
        source = '/- namespace Fake\n#print axioms fake\n-/\nnamespace N\ndef s := "end N"\n-- end N\n#print axioms f\nend N\n'
        self.assertEqual(r.audit(source, "'N.f' depends on axioms: []", module_name='Example'), 1)

    def test_private_qualified_to_active_namespace(self):
        source = 'namespace N\nprivate theorem f : True := by trivial\n#print axioms f\nend N\n'
        log = "'_private.Example.0.N.f' depends on axioms: []"
        self.assertEqual(r.audit(source, log, module_name='Example'), 1)
        with self.assertRaises(ValueError):
            r.audit(source, log, module_name='Other')
        with self.assertRaises(ValueError):
            r.audit(source, log + "\n'N.f' depends on axioms: []", module_name='Example')

    def test_reject_malformed_scope(self):
        with self.assertRaises(ValueError):
            r.audit('namespace N\nend Other\n#print axioms f\n', "'N.f' depends on axioms: []")

    def test_reject_alias_probes(self):
        with self.assertRaises(ValueError):
            r.audit('namespace N\n#print axioms f\n#print axioms N.f\nend N\n', "'N.f' depends on axioms: []")
        with self.assertRaises(ValueError):
            r.audit('namespace N\n#print axioms f\nend N\nnamespace M\n#print axioms f\nend M\n',
                    "'N.f' depends on axioms: []\n'M.f' depends on axioms: []")

if __name__ == '__main__':
    unittest.main()
