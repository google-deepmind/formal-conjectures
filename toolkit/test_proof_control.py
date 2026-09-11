"""Remote waiting and controller failure receipts."""
import contextlib
import io
import json
import subprocess
import unittest
from unittest.mock import patch
from conjectures import core, proof, cli, remote, exporter
from test_toolkit import ToolkitFixture

class ProofControlTests(ToolkitFixture):
    def test_wait_preserves_pending_cancellation(self):
        directory,record=core.start_run(self.root,'verify',executor={'repository':'fixture/repo'},remote_run_id=123)
        with patch.object(proof,'gh',side_effect=[b'{"status":"in_progress","conclusion":"","url":"https://example.com/run"}',b'',b'{"status":"in_progress","conclusion":"","url":"https://example.com/run"}']):
            requested=proof.control(directory,record,'cancel')
            self.assertIn('cancellation_requested_at',requested)
            waiting=proof.control(directory,requested,'wait')
        self.assertEqual(waiting['status'],'cancellation_requested')
        self.assertEqual(waiting['remote_status'],'in_progress')

    def test_installed_exporter_is_trusted_and_does_not_change_package_pins(self):
        self.repository()
        lakefile=self.root/'lakefile.toml'
        lakefile.write_text('name = "fixture"\n')
        original=lakefile.read_text()
        exporter.install_native(self.root)
        self.assertTrue((self.root/'comparator/ExportProblem.lean').is_file())
        self.assertTrue(lakefile.read_text().startswith(original))
        first=lakefile.read_bytes();exporter.install_native(self.root)
        self.assertEqual(first,lakefile.read_bytes())
        lakefile.write_text(lakefile.read_text().replace('root = "ExportProblem"','root = "CandidateCode"'))
        with self.assertRaisesRegex(ValueError,'incompatible'):exporter.install_native(self.root)

    def test_missing_remote_artifact_retains_infrastructure_error(self):
        directory,record=core.start_run(self.root,'verify',executor={'repository':'fixture/repo'},remote_run_id=123)
        with patch.object(proof,'gh',return_value=b'{"status":"completed","conclusion":"failure","url":"https://example.com/run"}'),patch.object(proof,'github',return_value={'artifacts':[]}):
            result=proof.control(directory,record,'wait')
        self.assertEqual(result['outcome'],'error')
        self.assertEqual(result['reason'],'missing_result')
        self.assertEqual(result['policy_outcome'],'not_evaluated')
        self.assertEqual(json.loads((directory/'run.json').read_text())['outcome'],'error')

    def test_cancel_completed_cancellation_is_confirmed_without_second_request(self):
        directory,record=core.start_run(self.root,'verify',executor={'repository':'fixture/repo'},remote_run_id=123)
        with patch.object(proof,'gh',return_value=b'{"status":"completed","conclusion":"cancelled","url":"https://example.com/run"}') as gh:
            self.assertEqual(proof.control(directory,record,'cancel')['outcome'],'cancelled')
            self.assertEqual(gh.call_count,1)

    def test_invalid_terminal_results_are_retained_as_errors(self):
        for outcome,conclusion,reason in [('unknown','success','invalid_result'),('pass','failure','incomplete_executor')]:
            directory,record=core.start_run(self.root,'verify',executor={'repository':'fixture/repo','commit':'a'*40},remote_run_id=123)
            core.save(directory/'request.json',{'id':'fixture'})
            core.save(directory/'remote/verification.json',{'request':{'id':'fixture'},'toolkit_commit':'a'*40,'outcome':outcome})
            with patch.object(proof,'gh',return_value=json.dumps({'status':'completed','conclusion':conclusion,'url':'https://example.com/run'}).encode()):
                value=proof.control(directory,record,'wait')
            self.assertEqual(value['outcome'],'error');self.assertEqual(value['reason'],reason)
            self.assertEqual(value['policy_outcome'],'not_evaluated')
            self.assertEqual(json.loads((directory/'run.json').read_text())['status'],'completed')

    def test_nonobject_remote_result_retains_unevaluated_error(self):
        for malformed in ([], None, 'pass'):
            directory,record=core.start_run(self.root,'verify',executor={'repository':'fixture/repo'},remote_run_id=123)
            core.save(directory/'remote/verification.json',malformed)
            with patch.object(proof,'gh',return_value=b'{"status":"completed","conclusion":"success","url":"https://example.com/run"}'):
                value=proof.control(directory,record,'wait')
            self.assertEqual(value['reason'],'invalid_result')
            self.assertEqual(value['policy_outcome'],'not_evaluated')
            self.assertEqual(json.loads((directory/'run.json').read_text())['outcome'],'error')

    def test_real_process_crash_and_missing_result_are_not_rejections(self):
        import sys
        for label,program in [('crash','import os, signal; os.kill(os.getpid(), signal.SIGKILL)'),('missing','print("disallowed_axiom: deliberately misleading diagnostic")')]:
            output=self.root/label;output.mkdir()
            with self.assertRaises(core.Failure) as error:
                remote.invoke_comparator([sys.executable,'-c',program],self.root,output)
            self.assertEqual(error.exception.reason,'missing_verifier_result')
            self.assertEqual(error.exception.code,3)
            self.assertTrue((output/'verifier.log').exists())

    def invoke(self,*args):
        out=io.StringIO();err=io.StringIO()
        with contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):code=cli.main(list(args))
        return code,out.getvalue(),err.getvalue()

    def test_wait_visibility_delay_then_result(self):
        directory,record=core.start_run(self.root,'verify');core.save(directory/'run.json',record)
        complete={**record,'status':'completed','outcome':'fail'}
        with patch.object(proof,'control',side_effect=[core.Failure('run_not_visible','wait',4),complete]),patch.object(proof.time,'sleep'):
            self.assertEqual(proof.wait(directory,record,30)['outcome'],'fail')
        with patch.object(proof,'control',return_value={**record,'status':'queued'}),patch.object(proof.time,'monotonic',side_effect=[0,1]):
            self.assertEqual(proof.wait(directory,record,1)['reason'],'wait_timeout')

    def test_interrupted_wait_never_cancels_remote(self):
        with patch.object(cli,'dispatch',side_effect=KeyboardInterrupt):
            code,out,err=self.invoke('run','wait','latest','--json')
        self.assertEqual(code,5);self.assertIn('remote work continues',json.loads(out)['message']);self.assertEqual(err,'')


    def test_init_uses_exact_checkout_and_requested_output_directory(self):
        from pathlib import Path
        from types import SimpleNamespace
        from conjectures import catalog
        self.repository()
        (self.root/'lakefile.toml').write_text('name = "fixture"\n')
        self.git('add','lakefile.toml');self.git('commit','-m','Pin fixture package')
        revision=self.git('rev-parse','HEAD').decode().strip()
        (self.root/'FormalConjectures/A.lean').write_text('uncommitted user edit')
        args=SimpleNamespace(target='original',repository=None,source_ref=None,catalog=None,out=self.root/'proof')
        real_command=core.command;real_git=core.git
        def command(argv,**kwargs):
            if argv[:1]==['lake']:return b''
            return real_command(argv,**kwargs)
        def git(root,*argv):
            if argv[:1]==('fetch',):return b''
            return real_git(root,*argv)
        def export(source,declaration,out,generator,rev,repo):
            self.assertEqual(source,source.resolve())
            self.assertIn('original',source.read_text())
            self.assertNotIn('uncommitted',source.read_text())
            target=out/'workspace';target.mkdir(parents=True)
            core.save(target/'fc-provenance.json',{'source':{'repository':repo,'commit':rev,'declaration':declaration,'module':'FormalConjectures.A','path':'FormalConjectures/A.lean'}})
            (target/'Submission.lean').write_text('theorem example : True := by trivial')
            return target
        with patch.object(proof,'public_repository',return_value='fixture/local'),patch.object(proof,'github',return_value={'sha':revision}),patch.object(proof,'checkout_tool',return_value=self.root),patch.object(catalog,'load',return_value={'provenance':{'source':{'repository':'fixture/local','commit':revision}},'problems':[{'theorem':'original','module':'FormalConjectures.A','githubPath':'FormalConjectures/A.lean'}]}),patch.object(proof,'command',side_effect=command),patch.object(proof,'git',side_effect=git),patch.object(exporter,'export',side_effect=export):
            result=proof.initialize(self.root,args,{})
        self.assertEqual(result['workspace'],str(args.out.resolve()))
        self.assertTrue((args.out/'Submission.lean').is_file())
        self.assertEqual((self.root/'FormalConjectures/A.lean').read_text(),'uncommitted user edit')
        self.assertEqual(self.git('rev-parse','HEAD').decode().strip(),revision)

    def test_qualification_error_has_a_retained_typed_record(self):
        self.repository()
        request={'run_id':'20260909T000000Z-aaaaaaaaaaaa','candidate_repository':'fixture/local','candidate_commit':'a'*40,'candidate_path':'.','source_repository':'https://github.com/fixture/local.git','source_commit':'a'*40,'source_path':'FormalConjectures/A.lean','declaration':'original'}
        with patch.object(remote,'qualify',side_effect=core.Failure('unqualified_executor','No AF_UNIX restriction',3)):
            value=remote.execute(request,self.root/'output',self.root,self.root,self.root,self.root)
        self.assertEqual(value['outcome'],'error');self.assertTrue((self.root/'output/verification.json').is_file())

    def test_dispatch_resolves_an_exact_lightweight_or_annotated_tag(self):
        sha='a'*40
        with patch.object(proof,'command',return_value=(sha+'\trefs/tags/toolkit-v0.2.0rc1\n').encode()):
            self.assertEqual(proof.executor_ref('fixture/repo',sha),'toolkit-v0.2.0rc1')
        with patch.object(proof,'command',return_value=('b'*40+'\trefs/tags/reviewed\n'+sha+'\trefs/tags/reviewed^{}\n').encode()):
            self.assertEqual(proof.executor_ref('fixture/repo',sha),'reviewed')
        with patch.object(proof,'command',return_value=b''):
            with self.assertRaises(core.Failure) as error:proof.executor_ref('fixture/repo',sha)
        self.assertEqual(error.exception.reason,'executor_tag_required')

    def test_source_dependency_failure_never_reaches_export_or_submission(self):
        self.repository()
        cache=self.root/'.lake';cache.mkdir();(cache/'rebuildable').write_text('dependency cache')
        request={'run_id':'20260909T000000Z-aaaaaaaaaaaa','candidate_repository':'fixture/local',
                 'candidate_commit':'a'*40,'candidate_path':'.','source_repository':'https://github.com/fixture/local.git',
                 'source_commit':'a'*40,'source_path':'FormalConjectures/A.lean','declaration':'original'}
        def unavailable(args,**kwargs):
            self.assertEqual(args,['lake','exe','cache','get'])
            self.assertEqual(kwargs['cwd'],self.root)
            kwargs['stdout'].write(b'dependency unavailable\n')
            raise subprocess.CalledProcessError(1,args)
        with patch.object(remote,'qualify'),patch.object(remote,'git',return_value=('a'*40).encode()), \
             patch.object(remote,'load_submission',return_value={'Submission.lean':b'candidate'}), \
             patch.object(exporter,'install_native'),patch.object(exporter,'export') as export, \
             patch.object(remote.subprocess,'run',side_effect=unavailable):
            value=remote.execute(request,self.root/'output',self.root,self.root,self.root,self.root)
        self.assertEqual(value['outcome'],'error');self.assertEqual(value['policy_outcome'],'not_evaluated')
        self.assertIn('dependency unavailable',(self.root/'output/source-dependencies.log').read_text())
        self.assertFalse(cache.exists())
        self.assertTrue((self.root/'FormalConjectures/A.lean').is_file())
        export.assert_not_called()
