import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from conjectures import core, proof, linux_executor, interface


class AgentProofTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve();self.candidate=self.root/'candidate';self.candidate.mkdir()
        self.target={'source':{'repository':'https://github.com/fixture/source.git','commit':'a'*40,
            'module':'FormalConjectures.A','path':'FormalConjectures/A.lean','declaration':'A'}}
        core.save(self.candidate/'fc-provenance.json',self.target)

    def test_workspace_discovery_does_not_relax_fc_operations(self):
        self.assertEqual(core.workspace(self.candidate,allow_proof=True),self.candidate)
        with self.assertRaises(core.Failure):core.workspace(self.candidate)

    def test_verify_checks_directory_before_target_or_executor(self):
        for candidate in (self.root/'missing',self.candidate/'fc-provenance.json'):
            with self.subTest(candidate=candidate):
                with self.assertRaises(core.Failure) as caught:proof.verify(self.root,candidate,{})
                self.assertEqual((caught.exception.reason,caught.exception.code),('directory_missing',2))

    def test_portable_target_binding_is_outside_submission(self):
        cache=self.root/'cache'
        core.save(cache/'targets'/f'{proof.rr.digest(str(self.candidate).encode())}.json',self.target)
        with patch.object(proof,'user_cache',return_value=cache),patch.object(linux_executor,'verify_local',return_value={'outcome':'pass'}) as execute:
            self.assertEqual(proof.verify(self.candidate,self.candidate,{'executor':{'kind':'linux'}})['outcome'],'pass')
            changed={'source':{**self.target['source'],'declaration':'easier'}}
            core.save(self.candidate/'fc-provenance.json',changed)
            with self.assertRaises(core.Failure) as caught:proof.verify(self.candidate,self.candidate,{'executor':{'kind':'linux'}})
            self.assertEqual(caught.exception.reason,'changed_target');self.assertEqual(execute.call_count,1)

    def test_local_submission_import_ignores_configuration_and_rejects_symlinks(self):
        (self.candidate/'Submission.lean').write_text('theorem t : True := by trivial')
        (self.candidate/'config.json').write_text('malicious config')
        self.assertEqual(list(linux_executor.submission_files(self.candidate)),['Submission.lean'])
        (self.candidate/'Submission').mkdir()
        (self.candidate/'Submission/secret.lean').symlink_to('/etc/passwd')
        with self.assertRaises(core.Failure):linux_executor.submission_files(self.candidate)

    def test_setup_failure_retains_unevaluated_result(self):
        with patch.object(linux_executor,'validate',side_effect=core.Failure('tool_pin_mismatch','changed tool',4)):
            result=linux_executor.verify_local(self.candidate,self.candidate,self.target,{'kind':'linux'})
        self.assertEqual(result['outcome'],'error');self.assertEqual(result['policy_outcome'],'not_evaluated')
        self.assertEqual(core.runs(self.candidate)[0]['reason'],'tool_pin_mismatch')

    def test_local_execution_reaches_dispatch_and_retains_missing_result(self):
        executor={'toolkit':str(self.root),'tools':str(self.root/'tools'),'ref':'a'*40,'binaries':{}}
        with patch.object(linux_executor,'validate'), \
             patch.object(linux_executor,'submission_files',return_value={'Submission.lean':b'example : True := by trivial'}), \
             patch.object(linux_executor,'git',return_value=('b'*40).encode()), \
             patch.object(linux_executor.subprocess,'run',return_value=__import__('types').SimpleNamespace(returncode=1)) as dispatch:
            result=linux_executor.verify_local(self.candidate,self.candidate,self.target,executor)
        dispatch.assert_called_once()
        self.assertEqual(dispatch.call_args.args[0][0],'systemd-run')
        self.assertEqual(result['reason'],'missing_result')
        self.assertEqual(result['outcome'],'error')
        self.assertEqual(result['policy_outcome'],'not_evaluated')

    def test_submission_read_rejects_a_concurrent_symlink_swap(self):
        path=self.candidate/'Submission.lean';path.write_text('candidate')
        outside=self.root/'private.lean';outside.write_text('outside submission')
        original=os.open
        def swapped(name,*args,**kwargs):
            if name=='Submission.lean':
                path.unlink();path.symlink_to(outside)
            return original(name,*args,**kwargs)
        with patch.object(linux_executor.os,'open',side_effect=swapped):
            with self.assertRaises(core.Failure) as caught:linux_executor.submission_files(self.candidate)
        self.assertEqual(caught.exception.reason,'disallowed_submission')

    def test_handoff_and_local_setup_arguments(self):
        proof.write_handoff(self.candidate,self.target)
        self.assertTrue((self.candidate/'AGENTS.md').is_file())
        self.assertIn('.conjectures/',(self.candidate/'.gitignore').read_text())
        args=interface.parse(['setup','verify','--local','--global','--toolkit','/opt/fc','--tools','/opt/tools','--json'])
        self.assertTrue(args.local);self.assertTrue(args.global_config)

    def test_formal_pass_keeps_semantic_assessment_visible(self):
        from conjectures import inspection, presentation, cli
        record={'id':'fixture','kind':'verify','status':'completed','outcome':'pass',
                'result':{'outcome':'pass','semantic_assessment_required':True,
                          'comparator':{'outcome':'pass','stage':'complete'}}}
        value=inspection.show(self.candidate,self.candidate,record,refresh=False)
        self.assertEqual(value['outcome'],'pass')
        self.assertTrue(value['verification_summary']['semantic_assessment_required'])
        self.assertIn('semantic assessment',value['next_action'])
        self.assertIn('Semantic assessment: required',presentation.render(value,interface.parse(['run','show','fixture'])))
        with patch.object(cli,'workspace',return_value=self.candidate),patch.object(cli,'config',return_value={}),patch.object(cli,'runs',return_value=[record]):
            status=cli.dispatch(interface.parse(['status']))
        self.assertEqual(status['outstanding'],1)
        self.assertIn('semantic assessment',status['next_actions'][0])
