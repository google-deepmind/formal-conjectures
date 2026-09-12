"""Designated publisher boundaries and operation/result separation."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from conjectures import publisher as p, core, report as rr

class PublisherTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        self.request={'request_id':'a'*32,'run_id':'20260910T000000Z-'+'b'*12,'pr':'42','archive_repository':'owner/archive','archive_commit':'c'*40,'manifest_sha256':'d'*64}
        self.target={'repository':'owner/fc','pr':42,'head':'e'*40,'base':'f'*40}
        self.run={'id':self.request['run_id'],'manifest_sha256':'d'*64,'kind':'review','target':self.target,
                  'created_at':'2026-09-10T00:00:00Z','url':'https://github.com/owner/archive/tree/'+'c'*40,
                  'summary':{'semantic_verdict':'CLEAN','completeness':'complete','findings':[]}}
        self.comments=[];self.observations=0;self.change_after=None
    def api(self,path):
        if '/pulls/' in path:
            self.observations+=1
            return {'state':'open','head':{'sha':'changed' if self.change_after and self.observations>=self.change_after else self.target['head']},'base':{'sha':self.target['base']}}
        return self.comments
    def execute(self):
        with patch('conjectures.evidence_reader.load',return_value={'status':'available','runs':[self.run]}),patch.object(p,'github',side_effect=self.api):
            return p.publish_comment(self.request,'owner/fc','owner/archive','evidence')
    def test_operator_comments_are_preserved_and_bot_publication_is_idempotent(self):
        self.comments=[{'id':1,'body':p.MARKER,'user':{'login':'operator','type':'User'}}]
        def write(endpoint,body,method):
            self.assertEqual(method,'POST')
            item={'id':2,'body':body,'user':{'login':'github-actions[bot]','type':'Bot'},'html_url':'https://github.com/owner/fc/pull/42#issuecomment-2'}
            self.comments.append(item);return item
        with patch.object(p,'write_comment',side_effect=write) as post:
            self.assertEqual(self.execute()['status'],'posted')
            self.assertEqual(self.execute()['status'],'posted')
            self.assertEqual(post.call_count,1)
        self.assertEqual(self.comments[0]['body'],p.MARKER)
    def test_head_changes_before_and_after_write_remain_historical(self):
        self.change_after=2
        with patch.object(p,'write_comment') as post:
            self.assertEqual(self.execute()['status'],'historical');post.assert_not_called()
        self.change_after=3;self.observations=0
        with patch.object(p,'write_comment',return_value={'id':3,'html_url':'https://github.com/owner/fc/pull/42#issuecomment-3'}):
            result=self.execute();self.assertEqual(result['status'],'historical');self.assertIn('comment_url',result)
    def test_newer_comment_and_unregistered_archive_do_not_post(self):
        self.comments=[{'id':1,'body':p.MARKER+'\n<!-- fc-review-order: 2999-01-01T00:00:00Z future -->','user':{'login':'github-actions[bot]','type':'Bot'}}]
        with patch.object(p,'write_comment') as post:
            self.assertEqual(self.execute()['status'],'superseded');post.assert_not_called()
        self.request['manifest_sha256']='0'*64
        with self.assertRaises(ValueError):self.execute()
    def test_noncanonical_pr_cannot_bypass_concurrency_group(self):
        self.request['pr']='042'
        with self.assertRaises(ValueError):self.execute()
    def test_cancelled_remote_operation_preserves_mathematical_record(self):
        record={'status':'completed','outcome':'fail'};core.save(self.root/'run.json',record)
        core.save(self.root/'publisher.json',{'request':self.request,'publisher':{'repository':'owner/fc','ref':'a'*40},'status':'queued','remote_run_id':1})
        def gh(*args):
            if args[:2]==('run','view') and '--json' in args:return rr.encode({'status':'completed','conclusion':'cancelled','url':'https://github.com/owner/fc/actions/runs/1'})
            raise core.Failure('missing_artifact','Cancelled before receipt',3)
        with patch.object(p,'gh',side_effect=gh):self.assertEqual(p.control(self.root,'wait')['command_status'],'cancelled')
        self.assertEqual(rr.read_json(self.root/'run.json'),record)
    def test_workflow_is_bundled_and_has_one_writer_without_candidate_checkout(self):
        root=Path(__file__).resolve().parents[1]
        workflow=(root/'.github/workflows/contribution-publisher.yml').read_bytes()
        self.assertEqual(workflow,(root/'toolkit/conjectures/resources/publisher-workflow.yml').read_bytes())
        self.assertIn(b'cancel-in-progress: false',workflow)
        self.assertIn(b'pull-requests: write',workflow)
        self.assertNotIn(b'pull_request.head',workflow)

    def test_wait_preserves_cancellation_request_until_confirmation(self):
        core.save(self.root/'publisher.json',{'request':self.request,'publisher':{'repository':'owner/fc','ref':'a'*40},'status':'queued','remote_run_id':1})
        pending=rr.encode({'status':'in_progress','conclusion':'','url':'https://example.com/run'})
        with patch.object(p,'gh',side_effect=[pending,b'',pending]):
            self.assertEqual(p.control(self.root,'cancel')['status'],'cancellation_requested')
            value=p.control(self.root,'wait')
            self.assertEqual(value['status'],'cancellation_requested')
            self.assertEqual(value['remote_status'],'in_progress')
