"""Case presentation preserves results while explaining current applicability."""
import copy
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from conjectures import inspection, presentation, review, report as rr, attributions
import test_review_lifecycle as lifecycle


class InspectionTests(unittest.TestCase):
    def setUp(self):
        self.fixture=lifecycle.ReviewLifecycleTests('test_complete_external_report_without_model_credentials')
        self.fixture.setUp();self.addCleanup(self.fixture.doCleanups)
        self.root=self.fixture.root;self.directory=self.fixture.directory
        self.complete=self.fixture.complete

    def test_show_findings_and_fresh_observation_without_changing_report(self):
        self.complete()
        before=(self.directory/'bundle/report.json').read_bytes()
        ticket={'repository':'owner/fc','pr':42,'head':'a'*40,'base':'b'*40}
        record={**rr.read_json(self.directory/'run.json'),'target':ticket}
        with patch.object(review,'github',return_value={'state':'open','head':{'sha':'c'*40},'base':{'sha':'b'*40}}):
            result=inspection.show(self.root,self.directory,record)
        self.assertEqual(result['outcome'],'pass')
        self.assertEqual(result['current_observation']['changes'],['head_changed'])
        self.assertEqual(result['current_applicability'],'historical')
        text=presentation.render(result,SimpleNamespace())
        self.assertIn('CLEAN',text);self.assertIn('head: reviewed',text)
        self.assertEqual((self.directory/'bundle/report.json').read_bytes(),before)

    def test_failed_observation_is_not_historical_or_current(self):
        with patch.object(review,'github',side_effect=OSError('offline')):
            value=review.observe(self.root,{'repository':'a/b','pr':1,'head':'a','base':'b'})
        self.assertEqual(value['applicability'],'unconfirmed')
        self.assertEqual(value['reason'],'freshness_unavailable')

    def test_attribution_is_request_bound_and_names_shared_context(self):
        value={'schema_version':'fc.reviewer-attribution.v1','request_id':'request','reviewers':[{
            'kind':'ai','name':'Helper','method':'source comparison','scope':['A.lean'],
            'independence':'shared_dependencies','shared_dependencies':['same source dossier'],
            'evidence':rr.descriptors({'finding.txt':b'finding'})}]}
        self.assertEqual(attributions.validate(value,'request',lambda _:b'finding'),value)
        with self.assertRaises(ValueError):attributions.validate(value,'other',lambda _:b'finding')
        with self.assertRaises(ValueError):attributions.validate(value,'request',lambda _:b'changed')
        bad=copy.deepcopy(value);bad['reviewers'][0]['shared_dependencies']=[]
        with self.assertRaises(ValueError):attributions.validate(bad,'request',lambda _:b'finding')

    def test_inspected_failure_points_to_logs_instead_of_itself(self):
        record={'id':'case','kind':'verify','status':'completed','outcome':'error',
                'verification_summary':{'policy_outcome':'not_evaluated'}}
        self.assertIn('run logs case',inspection.next_action(record))
        self.assertNotIn('run show case',inspection.next_action(record))
