import copy
import tempfile
import tomllib
import unittest
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch
from conjectures import evaluation, eval_verifier, core


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
                'cases':[{'id':'plain','declaration':'Fixture.plain','exposure':'Development fixture'}]}

    def test_frozen_suite_rejects_floating_pins_duplicate_tasks_and_missing_exposure(self):
        suite=self.suite();evaluation.validate_suite(suite)
        mutations=[lambda x:x['execution'].update(solver_image='image:latest'),
                   lambda x:x['cases'].append(x['cases'][0]),lambda x:x['cases'][0].pop('exposure'),
                   lambda x:x['source'].update(commit='main')]
        for mutate in mutations:
            value=copy.deepcopy(suite);mutate(value)
            with self.assertRaises(ValueError):evaluation.validate_suite(value)

    def test_harbor_task_has_separate_verifier_and_only_submission_artifacts(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'environment').mkdir()
            target={'id':'plain','source':{'declaration':'Fixture.plain'},'suite_sha256':'a'*64,'exposure':'known'}
            evaluation.write_task(root,target,self.suite()['execution'])
            config=tomllib.loads((root/'task.toml').read_text())
            self.assertEqual(config['verifier']['environment_mode'],'separate')
            self.assertEqual(config['artifacts'],['/app/Submission.lean','/app/Submission'])
            self.assertFalse((root/'solution').exists())
            self.assertIn('PYTHONPATH=/opt/fc/toolkit',(root/'tests/test.sh').read_text())

    def test_infrastructure_failure_never_emits_zero_reward(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);target=root/'target.json'
            core.save(target,{'schema_version':'fc.proof-task.v1','id':'case','suite_sha256':'a'*64})
            with patch.object(eval_verifier,'restrict',side_effect=core.Failure('unqualified_executor','missing sandbox',3)):
                result=eval_verifier.run(target,root,root/'result')
            self.assertEqual(result['status'],'error')
            self.assertFalse((root/'result/reward.txt').exists())
            self.assertEqual(evaluation.summarize(root)['counts']['error'],1)
            with self.assertRaises(core.Failure):eval_verifier.run(target,root,root/'result')

    def test_export_is_atomic_and_does_not_create_operator_runs(self):
        from conjectures import proof,catalog
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);suite=self.suite();suite_path=root/'suite.json';core.save(suite_path,suite)
            data={'schemaVersion':2,'provenance':{'source':suite['source']},'problems':[
                {'theorem':'Fixture.plain','module':'FormalConjectures.Example','statement':'True'}]}
            args=SimpleNamespace(suite=suite_path,out=root/'tasks',catalog=None)
            def generate(repo,problem,repository,revision,artifact):
                self.assertEqual(repository,suite['source']['repository']);self.assertEqual(revision,'a'*40)
                workspace=artifact/'workspace';workspace.mkdir(parents=True)
                core.save(workspace/'fc-provenance.json',{'source':{'repository':'https://github.com/fixture/fc.git',
                    'commit':revision,'module':problem['module'],'path':problem['githubPath'],'declaration':problem['theorem']}})
                core.save(workspace/'config.json',{'definition_names':['answer']})
                (workspace/'Submission.lean').write_text('def answer := sorry')
                return workspace
            with patch.object(catalog,'load',return_value=data),patch.object(proof,'generate',side_effect=generate),patch.object(proof,'start_run',side_effect=AssertionError('No operator run')):
                value=evaluation.export(None,args)
            target=core.rr.read_json(args.out/'plain/tests/target.json')
            self.assertTrue(target['semantic_assessment_required'])
            self.assertTrue((args.out/'manifest.json').is_file())
            self.assertFalse(list(args.out.rglob('.conjectures')))
            args.out=root/'failed'
            with patch.object(catalog,'load',return_value=data),patch.object(proof,'generate',side_effect=core.Failure('export_failed','fixture',3)):
                with self.assertRaises(core.Failure):evaluation.export(None,args)
            self.assertFalse(args.out.exists())
