"""Publication against disposable git archives; no live comments or uploads."""
import subprocess
from pathlib import Path
from unittest.mock import patch
import unittest
import shutil
import threading
from concurrent.futures import ThreadPoolExecutor
from conjectures import core, evidence, report as rr, review
import test_review_lifecycle as lifecycle


class CatalogEvidenceTests(unittest.TestCase):
    def test_exact_repository_revision_and_variant_joins(self):
        from conjectures.projections import evidence_for
        from test_catalog import native
        problem={**native()['problems'][0],'githubPath':'FormalConjectures/ErdosProblems/92.lean'}
        run={'kind':'verify','target':{'repository':'owner/fc','commit':'a'*40,
             'module':problem['module'],'declaration':problem['theorem']},'created_at':'today'}
        index={'runs':[run]}
        self.assertEqual(evidence_for(problem,index,'a'*40,'owner/fc')[0]['applicability'],'current')
        self.assertEqual(evidence_for(problem,index,'c'*40,'owner/fc')[0]['applicability'],'historical')
        self.assertEqual(evidence_for(problem,index,'a'*40,'other/fc'),[])
        self.assertEqual(evidence_for({**problem,'theorem':'weak'},index,'a'*40,'owner/fc'),[])
        self.assertEqual(evidence_for(problem,index,'a'*40)[0]['applicability'],'unconfirmed')
        run['target']['repository']='https://github.com/owner/fc.git'
        run['target']['module']='«FormalConjectures».«ErdosProblems».«92»'
        self.assertEqual(evidence_for(problem,index,'a'*40,'owner/fc')[0]['applicability'],'current')



class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.fixture=lifecycle.ReviewLifecycleTests('test_complete_external_report_without_model_credentials')
        self.fixture.setUp();self.addCleanup(self.fixture.doCleanups)
        f=self.fixture;self.root=f.root;self.directory=f.directory
        with patch.object(review,'applicability',return_value='current'):f.complete()
        ticket=rr.read_json(f.directory/'ticket.json');ticket.update(local_snapshot=False,pr=42)
        core.save(f.directory/'ticket.json',ticket)
        self.ticket=ticket
        archive=self.root/'archive';subprocess.run(['git','init','-q',str(archive)],check=True)
        for key,value in [('user.name','Fixture'),('user.email','fixture@example.invalid')]:core.git(archive,'config',key,value)
        (archive/'README.md').write_text('Disposable evidence archive')
        core.git(archive,'add','.');core.git(archive,'commit','-qm','Archive root');core.git(archive,'branch','-M','evidence')
        self.remote=self.root/'remote.git';subprocess.run(['git','clone','-q','--bare',str(archive),str(self.remote)],check=True)
        self.cfg={'evidence':{'repository':'fixture/archive','branch':'evidence'}}
        self.real_command=core.command

    def command(self,args,**kwargs):
        args=list(args)
        if args[:2]==['git','clone']:
            args=[str(self.remote) if x=='https://github.com/fixture/archive.git' else x for x in args]
        return self.real_command(args,**kwargs)

    def github(self,path):
        if '/commits/' in path:return {'sha':path.rsplit('/',1)[1]}
        return {'private':False}

    def publish(self):
        with patch.object(evidence,'github',side_effect=self.github),patch.object(evidence,'command',side_effect=self.command),patch.dict('os.environ',{'GIT_AUTHOR_NAME':'Fixture','GIT_AUTHOR_EMAIL':'fixture@example.invalid','GIT_COMMITTER_NAME':'Fixture','GIT_COMMITTER_EMAIL':'fixture@example.invalid'}):
            return evidence.publish(self.root,self.directory,self.cfg)

    def test_archive_is_idempotent_and_export_omits_raw_material(self):
        first=self.publish();second=self.publish();self.assertEqual(first,second)
        manifest=rr.read_json(self.directory/'public/manifest.json')
        paths=[a['path'] for a in manifest['artifacts']]
        self.assertNotIn('snapshot',paths);self.assertNotIn('build.log',paths)
        self.assertTrue((self.directory/'public/redactions.json').is_file())
        original=rr.read_json(self.directory/'run.json');self.assertEqual(original['outcome'],'pass')

    def test_failed_upload_is_not_advertised(self):
        original=evidence.git
        def git(root,*args):
            if args and args[0]=='push':raise core.Failure('execution_error','simulated rejected push',3)
            return original(root,*args)
        with patch.object(evidence,'git',side_effect=git),self.assertRaises(core.Failure):self.publish()
        self.assertFalse((self.directory/'publication.json').exists())
        self.assertEqual(rr.read_json(self.directory/'run.json')['status'],'completed')
        self.publish()  # Retry checks immutable bytes and completes.

    def test_concurrent_archives_preserve_both_runs_after_explicit_retry(self):
        other=self.root/'second-run';shutil.copytree(self.directory,other)
        record=rr.read_json(other/'run.json');record['id']='20260909T000000Z-222222222222'
        core.save(other/'run.json',record)
        barrier=threading.Barrier(2);original=evidence.git
        def git(root,*args):
            if args and args[0]=='push':barrier.wait(timeout=10)
            return original(root,*args)
        def publish(directory):
            try:return evidence.publish(self.root,directory,self.cfg)
            except core.Failure as error:return error
        with patch.object(evidence,'github',side_effect=self.github),patch.object(evidence,'command',side_effect=self.command),patch.object(evidence,'git',side_effect=git),patch.dict('os.environ',{'GIT_AUTHOR_NAME':'Fixture','GIT_AUTHOR_EMAIL':'fixture@example.invalid','GIT_COMMITTER_NAME':'Fixture','GIT_COMMITTER_EMAIL':'fixture@example.invalid'}):
            with ThreadPoolExecutor(max_workers=2) as pool:
                results=list(pool.map(publish,[self.directory,other]))
        self.assertEqual(sum(isinstance(r,core.Failure) for r in results),1)
        failed=[self.directory,other][next(i for i,r in enumerate(results) if isinstance(r,core.Failure))]
        self.assertFalse((failed/'publication.json').exists())
        with patch.object(evidence,'github',side_effect=self.github),patch.object(evidence,'command',side_effect=self.command),patch.dict('os.environ',{'GIT_AUTHOR_NAME':'Fixture','GIT_AUTHOR_EMAIL':'fixture@example.invalid','GIT_COMMITTER_NAME':'Fixture','GIT_COMMITTER_EMAIL':'fixture@example.invalid'}):
            evidence.publish(self.root,failed,self.cfg)
        index=rr.parse(core.git(self.remote,'show','evidence:toolkit-index.json'))
        self.assertEqual({r['id'] for r in index['runs']},{rr.read_json(self.directory/'run.json')['id'],record['id']})

    def test_stale_target_never_posts(self):
        with patch.object(evidence,'github',return_value={'state':'open','head':{'sha':'changed'},'base':{'sha':self.ticket['base']}}),patch.object(evidence,'gh') as post:
            with self.assertRaises(core.Failure) as error:evidence.post(self.directory,{'url':'https://example.invalid/archive'})
        self.assertEqual(error.exception.reason,'stale_target');post.assert_not_called()

    def test_older_request_cannot_replace_newer_comment(self):
        def api(path):
            if '/pulls/' in path:return {'state':'open','head':{'sha':self.ticket['head']},'base':{'sha':self.ticket['base']}}
            if path=='user':return {'login':'fixture'}
            return [{'id':1,'user':{'login':'fixture'},'body':evidence.MARKER+'\n<!-- fc-review-order: 2999-01-01T00:00:00Z newer -->'}]
        with patch.object(evidence,'github',side_effect=api),patch.object(evidence,'gh') as post:
            with self.assertRaises(core.Failure) as error:evidence.post(self.directory,{'url':'https://example.invalid/archive'})
        self.assertEqual(error.exception.reason,'older_request');post.assert_not_called()

if __name__=='__main__':unittest.main()
