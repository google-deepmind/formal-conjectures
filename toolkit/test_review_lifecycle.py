"""Observable preparation, report completion and independent receipt boundaries."""
import copy
import json
import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from conjectures import cli, core, report as rr, review

class ReviewLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        self.git('init','-q');self.git('config','user.name','Fixture');self.git('config','user.email','fixture@invalid')
        (self.root/'.gitignore').write_text('.conjectures/\n')
        (self.root/'FormalConjectures').mkdir()
        self.candidate=self.root/'FormalConjectures/A.lean';self.candidate.write_text('theorem a : True := by trivial\n')
        self.git('add','.');self.git('commit','-qm','base');self.base=self.git('rev-parse','HEAD').decode().strip()
        self.candidate.write_text('theorem a : True := True.intro\n')
        self.git('add','.');self.git('commit','-qm','candidate')
        self.directory,self.record=core.start_run(self.root,'review')
        source=self.root/'.conjectures/source';source.mkdir();(source/'problem.txt').write_text('Source: True holds.')
        review.prepare(self.root,self.directory,base=self.base,repository="fixture/local",supplied=source)
        with patch.object(review,'build',side_effect=self.build):
            self.record=review.handoff(self.directory,{},self.record)
        self.result=rr.read_json(self.directory/'review-template.json')
        self.result.update(reviewer='Existing agent; model unknown',questions=[],coverage={k:'complete' for k in rr.ANGLES})
        self.report=self.root/'.conjectures/review.json';core.save(self.report,self.result)
    def git(self,*args):
        return subprocess.check_output(['git','-C',str(self.root),*args])
    def build(self,directory,cfg):
        request,_,_=review.load(directory)
        receipt={'request_id':request['id'],'image':'sha256:'+'a'*64,'exit_code':0,
                 'command':['lake','--wfail','build','FormalConjectures.A'],'output':'pass','policy':'scoped-build.v1'}
        core.save(directory/'controller/build.json',receipt)
        return 'pass',receipt
    def complete(self,**kwargs):
        return review.complete(self.root,self.directory,self.record,self.report,**kwargs)
    def test_preparation_waits_for_review_without_importing_model_runtime(self):
        self.assertEqual(self.record['status'],'awaiting_review')
        self.assertEqual(self.record['outcome'],'incomplete')
        self.assertFalse((self.directory/'bundle').exists())
        self.assertTrue(Path(self.record['paths']['template']).is_file())
        self.assertFalse(any(name in __import__('sys').modules for name in ('conjectures.codex','conjectures.eval_workspace','mcp')))
    def test_complete_external_report_without_model_credentials(self):
        with patch.dict(os.environ,{},clear=True):result=self.complete()
        self.assertEqual(result['outcome'],'pass');self.assertEqual(result['status'],'completed')
        self.assertTrue(Path(result['report']).is_file())
        bundle=rr.read_json(self.directory/'bundle/report.json')
        self.assertEqual(bundle['checks'][0]['status'],'pass')
        self.assertEqual(bundle['review']['reviewer'],'Existing agent; model unknown')
        self.assertEqual(rr.assemble(self.directory/'input',self.directory/'input',self.directory/'review.json',self.directory/'evidence')['report.json'],(self.directory/'bundle/report.json').read_bytes())
    def test_invalid_report_is_correctable_and_cannot_publish(self):
        bad=copy.deepcopy(self.result);bad['request_id']='wrong';core.save(self.report,bad)
        with self.assertRaises(ValueError):self.complete()
        self.assertEqual(rr.read_json(self.directory/'run.json')['status'],'awaiting_review')
        self.assertFalse((self.directory/'evidence').exists())
        if importlib.util.find_spec('conjectures.evidence'):
            from conjectures.evidence import export
            with self.assertRaises(core.Failure):export(self.root,self.directory)
        core.save(self.report,self.result);self.assertEqual(self.complete()['outcome'],'pass')
    def test_supplied_checks_cannot_override_controller(self):
        receipt=rr.read_json(self.directory/'controller/build.json');receipt['exit_code']=1
        core.save(self.directory/'controller/build.json',receipt)
        self.record['build_receipt_sha256']=rr.digest((self.directory/'controller/build.json').read_bytes())
        supplied=self.root/'.conjectures/operator';supplied.mkdir()
        (supplied/'checks.json').write_text('{"checks":[{"kind":"build","status":"pass"}]}')
        result=self.complete(supplied=supplied)
        self.assertEqual(result['outcome'],'fail')
        bundle=rr.read_json(self.directory/'bundle/report.json')
        self.assertEqual(bundle['checks'][0]['status'],'fail')
        self.assertTrue((self.directory/'bundle/evidence/operator/checks.json').exists())
    def test_tampered_receipt_is_rejected(self):
        (self.directory/'controller/build.json').write_text('{}')
        with self.assertRaises(core.Failure) as error:self.complete()
        self.assertEqual(error.exception.reason,'changed_build_receipt')
    def test_missing_sources_force_incomplete_coverage(self):
        ticket=rr.read_json(self.directory/'ticket.json');ticket['source_collection']['coverage']='incomplete'
        core.save(self.directory/'ticket.json',ticket)
        self.assertEqual(self.complete()['outcome'],'incomplete')
        self.assertEqual(rr.read_json(self.directory/'review.json')['coverage']['source-fidelity'],'incomplete')
    def test_changed_local_input_is_historical(self):
        self.candidate.write_text('changed again\n')
        result=self.complete()
        self.assertEqual(result['applicability'],'historical');self.assertEqual(result['outcome'],'incomplete')
        self.assertIn('STALE',(self.directory/'bundle/summary.md').read_text())
    def test_completed_run_cannot_be_overwritten(self):
        self.complete();before=(self.directory/'bundle/report.json').read_bytes()
        with self.assertRaises(core.Failure):self.complete()
        self.assertEqual((self.directory/'bundle/report.json').read_bytes(),before)
    def test_scratch_restores_original_input_and_cannot_change_receipt(self):
        original=(self.directory/'controller/build.json').read_bytes()
        (self.directory/'snapshot/FormalConjectures/A.lean').write_text('poisoned readable copy')
        def isolated(image,path):
            self.assertEqual((path/'FormalConjectures/A.lean').read_text(),self.candidate.read_text())
            return 'scratch'
        cfg={'limits':{'scratch_calls':20,'scratch_seconds':60}}
        with patch.object(review,'check_environment'),patch.object(review.ex,'isolated',side_effect=isolated),patch.object(review.ex,'execute',return_value={'exit_code':0,'output':'scratch pass'}),patch.object(review.ex,'run'):
            result=review.scratch(self.directory,cfg,self.record,['sh','-c','echo scratch'])
        self.assertEqual(result['purpose'],'scratch_only')
        self.assertEqual((self.directory/'controller/build.json').read_bytes(),original)
        self.complete()
        self.assertEqual(rr.read_json(self.directory/'bundle/report.json')['checks'][0]['evidence'],['evidence/build.json'])
    def test_replay_creates_a_new_build_and_keeps_source_request(self):
        directory,record=core.start_run(self.root,'review')
        review.replay(self.directory,directory)
        with patch.object(review,'build',side_effect=self.build) as build:
            pending=review.handoff(directory,{},record)
        build.assert_called_once()
        self.assertEqual(pending['request_id'],self.record['request_id'])
        self.assertNotEqual(pending['id'],self.record['id'])
    def test_operator_links_and_unknown_references_are_rejected(self):
        supplied=self.root/'.conjectures/operator';supplied.mkdir()
        (supplied/'secret').symlink_to(self.report)
        with self.assertRaises(core.Failure):self.complete(supplied=supplied)
        bad=copy.deepcopy(self.result);bad['findings']=[dict(angle='source-fidelity',file='FormalConjectures/A.lean',line=1,severity='semantic',message='Claim',suggestion='Fix',evidence=['evidence/not-retained.txt'])]
        core.save(self.report,bad)
        with self.assertRaises(ValueError):self.complete()
    def test_doctor_and_config_do_not_depend_on_ai_authentication(self):
        (self.root/'.conjectures/config.json').write_text('{"backend":"codex","model":"obsolete"}')
        with patch.object(Path,'home',return_value=self.root),patch.dict(os.environ,{},clear=True):
            cfg=core.config(self.root);result=cli.doctor(self.root,cfg)
        self.assertNotIn('model',cfg);self.assertNotIn('backend',cfg)
        self.assertNotIn('codex',result['tools']);self.assertNotIn('codex_oauth_available',result)
    def test_run_lock_rejects_concurrent_mutation(self):
        with core.run_lock(self.directory), self.assertRaises(core.Failure) as error:
            with core.run_lock(self.directory):pass
        self.assertEqual(error.exception.reason,'run_busy')

if __name__=='__main__':unittest.main()
