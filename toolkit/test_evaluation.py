import copy
import tempfile
import tomllib
import unittest
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch
from conjectures import evaluation, eval_suite, eval_verifier, core


class EvaluationTests(unittest.TestCase):
    def test_summarize_rejects_malformed_results_without_counting_them(self):
        valid={'schema_version':'fc.proof-eval-result.v1','status':'verified','task':'case','suite_sha256':'a'*64}
        invalid=[[],{**valid,'status':[]},{k:v for k,v in valid.items() if k!='task'},
                 {**valid,'task':42},{**valid,'suite_sha256':'not-a-digest'},
                 {**valid,'suite_sha256':None}]
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            for value in invalid:
                with self.subTest(value=value):
                    core.save(root/'fc-result.json',value)
                    with self.assertRaises(core.Failure) as caught:evaluation.summarize(root)
                    self.assertEqual((caught.exception.reason,caught.exception.code),('invalid_result',3))
            core.save(root/'fc-result.json',{**valid,'status':'error','task':'unknown','suite_sha256':None})
            self.assertEqual(evaluation.summarize(root)['counts']['error'],1)

    def suite(self):
        return {'schema_version':evaluation.SCHEMA,'source':{'repository':'fixture/fc','commit':'a'*40},
                'execution':{'solver_image':'example/solver@sha256:'+'b'*64,'verifier_image':'example/verifier@sha256:'+'c'*64,
                             'toolkit_commit':'d'*40,'agent_seconds':600},
                'cases':[{'id':'plain','declaration':'Fixture.plain','path':'FormalConjectures/Example.lean',
                          'exposure':'Development fixture'}]}

    def test_frozen_suite_rejects_floating_pins_duplicate_tasks_and_missing_fields(self):
        suite=self.suite();evaluation.validate_suite(suite)
        mutations=[lambda x:x['execution'].update(solver_image='image:latest'),
                   lambda x:x['cases'].append(x['cases'][0]),lambda x:x['cases'][0].pop('exposure'),
                   lambda x:x['cases'][0].pop('path'),lambda x:x['cases'][0].update(path='../escape.lean'),
                   lambda x:x['source'].update(commit='main')]
        for mutate in mutations:
            value=copy.deepcopy(suite);mutate(value)
            with self.assertRaises(ValueError):evaluation.validate_suite(value)

    def test_suite_core_excludes_images_budgets_and_exposure(self):
        suite=self.suite();value=eval_suite.core(suite)
        changed=copy.deepcopy(suite);changed['execution']['agent_seconds']=60;changed['cases'][0]['exposure']='other'
        self.assertEqual(eval_suite.core_digest(value),eval_suite.core_digest(eval_suite.core(changed)))
        changed['cases'][0]['declaration']='Fixture.other'
        self.assertNotEqual(eval_suite.core_digest(value),eval_suite.core_digest(eval_suite.core(changed)))

    def test_harbor_task_uses_prebuilt_offline_verifier_and_only_submission_artifacts(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'environment').mkdir()
            target={'id':'plain','source':{'declaration':'Fixture.plain'},'suite_sha256':'a'*64,'core_sha256':'e'*64,
                    'exposure':'known','semantic_assessment_required':False}
            execution=self.suite()['execution']
            evaluation.write_task(root,target,execution)
            config=tomllib.loads((root/'task.toml').read_text())
            self.assertEqual(config['verifier']['environment_mode'],'separate')
            self.assertEqual(config['verifier']['environment']['docker_image'],execution['verifier_image'])
            self.assertEqual(config['verifier']['environment']['network_mode'],'no-network')
            self.assertEqual(config['verifier']['env'],{'FC_EVAL_CASE':'plain','FC_EVAL_SUITE_SHA256':'a'*64,'FC_EVAL_CORE_SHA256':'e'*64})
            self.assertEqual(config['artifacts'],['/app/Submission.lean','/app/Submission'])
            self.assertFalse((root/'solution').exists())
            self.assertIn('/opt/fc-suite/packages',(root/'environment/Dockerfile').read_text())
            self.assertIn(execution['solver_image'],(root/'environment/Dockerfile').read_text())
            self.assertFalse((root/'tests/Dockerfile').exists())

    def test_verifier_binding_failures_never_emit_a_reward(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);suite=root/'suite';value=eval_suite.core(self.suite())
            digest=eval_suite.core_digest(value)
            core.save(suite/'suite-core.json',value)
            core.save(suite/'cases/plain/target.json',{'schema_version':eval_suite.CASE,'id':'plain','core_sha256':digest,
                                                       'source':{},'toolkit_commit':'d'*40,'semantic_assessment_required':False})
            cases=[('plain','a'*64,'f'*64,'suite_binding_mismatch'),('plain',None,digest,'invalid_input'),
                   ('../escape','a'*64,digest,'invalid_input')]
            for index,(case,suite_sha,core_sha,reason) in enumerate(cases):
                with self.subTest(reason=reason,case=case):
                    out=root/f'result-{index}'
                    with patch.object(eval_verifier,'restrict',side_effect=AssertionError('restriction must follow binding checks')):
                        result=eval_verifier.run(case,root,out,suite_sha,core_sha,suite=suite)
                    self.assertEqual(result['status'],'error')
                    self.assertFalse((out/'reward.txt').exists())
            out=root/'result-sandbox'
            with patch.object(eval_verifier,'restrict',side_effect=core.Failure('unqualified_executor','missing sandbox',3)):
                result=eval_verifier.run('plain',root,out,'a'*64,digest,suite=suite)
            self.assertEqual((result['status'],result['reason']),('error','unqualified_executor'))
            self.assertFalse((out/'reward.txt').exists())
            self.assertEqual(evaluation.summarize(out)['counts']['error'],1)
            with self.assertRaises(core.Failure):eval_verifier.run('plain',root,out,'a'*64,digest,suite=suite)

    def test_export_uses_image_workspaces_and_rejects_another_suite_core(self):
        from conjectures import proof
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);suite=self.suite();suite_path=root/'suite.json';core.save(suite_path,suite)
            value=eval_suite.core(suite);digest=eval_suite.core_digest(value)
            def image_files(image,paths,destination,core_value=value):
                self.assertEqual(image,suite['execution']['verifier_image'])
                core.save(destination/'suite-core.json',core_value)
                baked=destination/'cases/plain'
                core.save(baked/'target.json',{'schema_version':eval_suite.CASE,'id':'plain','core_sha256':digest,
                    'source':{'repository':'https://github.com/fixture/fc.git','commit':'a'*40,'path':'FormalConjectures/Example.lean',
                              'module':'FormalConjectures.Example','declaration':'Fixture.plain'},
                    'toolkit_commit':'d'*40,'semantic_assessment_required':True})
                core.save(baked/'workspace/fc-provenance.json',{'source':{'declaration':'Fixture.plain','module':'FormalConjectures.Example','repository':'https://github.com/fixture/fc.git','commit':'a'*40,'path':'FormalConjectures/Example.lean'}})
                (baked/'workspace/Submission.lean').write_text('def answer := sorry')
                (baked/'workspace/.lake/build').mkdir(parents=True)
            args=SimpleNamespace(suite=suite_path,out=root/'tasks')
            with patch.object(evaluation,'image_files',side_effect=image_files),patch.object(proof,'start_run',side_effect=AssertionError('No operator run')):
                evaluation.export(None,args)
            config=tomllib.loads((args.out/'plain/task.toml').read_text())
            self.assertTrue(config['metadata']['semantic_assessment_required'])
            self.assertTrue((args.out/'plain/environment/workspace/Submission.lean').is_file())
            self.assertFalse((args.out/'plain/environment/workspace/.lake').exists())
            self.assertTrue((args.out/'manifest.json').is_file())
            self.assertFalse(list(args.out.rglob('.conjectures')))
            other={**value,'cases':[{**value['cases'][0],'declaration':'Fixture.other'}]}
            args.out=root/'mismatch'
            with patch.object(evaluation,'image_files',side_effect=lambda i,p,dest:image_files(i,p,dest,other)):
                with self.assertRaises(core.Failure) as caught:evaluation.export(None,args)
            self.assertEqual(caught.exception.reason,'suite_image_mismatch')
            self.assertFalse(args.out.exists())


if __name__=='__main__':unittest.main()
