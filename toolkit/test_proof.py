"""Exact submission and typed-verifier boundary checks."""
import unittest
from conjectures import core, remote
from test_toolkit import ToolkitFixture

class ProofTests(ToolkitFixture):
    def test_typed_rejection_is_not_an_execution_error(self):
        value=remote.typed_result(b'{"schemaVersion":1,"outcome":"rejected","reason":"illegal_axiom","stage":"axioms"}',1)
        self.assertEqual(value['outcome'],'rejected')

    def test_log_words_cannot_establish_a_verdict(self):
        with self.assertRaises(ValueError):remote.typed_result(b'Illegal axiom sorryAx',1)
        with self.assertRaises(core.Failure):remote.typed_result(b'{"schemaVersion":1,"outcome":"pass","stage":"complete","reason":"verified"}',1)

    def test_remote_never_imports_candidate_config(self):
        self.repository()
        for name in ['Submission.lean','Challenge.lean','lakefile.toml','config.json']:(self.root/name).write_text(name)
        self.git('add','.');self.git('commit','-qm','candidate')
        actual=remote.load_submission(self.root,self.git('rev-parse','HEAD').decode().strip(),'.')
        self.assertEqual(actual,{'Submission.lean':b'Submission.lean'})

    def test_remote_rejects_submission_symlinks(self):
        self.repository();(self.root/'Submission.lean').symlink_to('/etc/passwd')
        self.git('add','.');self.git('commit','-qm','candidate')
        with self.assertRaises(core.Failure):remote.load_submission(self.root,self.git('rev-parse','HEAD').decode().strip(),'.')

