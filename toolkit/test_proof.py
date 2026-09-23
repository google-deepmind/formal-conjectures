"""Exact submission and typed-verifier boundary checks."""
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from conjectures import report as rr
from conjectures import core, remote
from test_toolkit import ToolkitFixture

class ProofTests(ToolkitFixture):
    def test_historical_4884_invocation_error_cannot_become_policy_rejection(self):
        retained=rr.read_json(Path(__file__).parent/'fixtures/comparator-4884.json')
        self.assertEqual(retained['policy_result']['outcome'],'not_evaluated')
        def failed(*args,**kwargs):
            kwargs['stdout'].write(b'error: illegal axiom (synthetic diagnostic)')
            return SimpleNamespace(returncode=retained['invocation']['exit_code'])
        with patch.object(remote.subprocess,'run',side_effect=failed):
            with self.assertRaises(core.Failure) as error:remote.invoke_comparator(['comparator'],self.root,self.root)
        self.assertEqual(error.exception.code,3)
        self.assertEqual(error.exception.reason,'missing_verifier_result')
        self.assertTrue((self.root/'verifier.log').is_file())

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

