"""Consumer validation rejects drift instead of displaying unchecked outcomes."""
import copy
import unittest
from unittest.mock import patch
from conjectures import evidence_reader as reader, evidence, report as rr, core
import test_review_lifecycle as lifecycle


class EvidenceReaderTests(unittest.TestCase):
    def setUp(self):
        f=lifecycle.ReviewLifecycleTests('test_complete_external_report_without_model_credentials')
        f.setUp();self.addCleanup(f.doCleanups);self.root=f.root
        f.complete()
        ticket=rr.read_json(f.directory/'ticket.json');ticket.update(local_snapshot=False,pr=42)
        core.save(f.directory/'ticket.json',ticket)
        with patch.object(evidence,'github',return_value={'private':False}):files,record=evidence.export(f.root,f.directory)
        prefix='runs/'+record['id'];self.files={prefix+'/'+k:v for k,v in files.items()}
        self.entry={k:record[k] for k in ('id','kind','outcome','target','created_at','producer')}
        self.entry.update(path=prefix,manifest_sha256=rr.digest(files['manifest.json']),scope=rr.read_json(f.directory/'input/request.json')['scope'])
        self.index={'schema_version':'fc.evidence-index.v1','runs':[self.entry]}
        self.origin={'repository':'owner/evidence','commit':'c'*40}

    def test_valid_bundle_has_pinned_link_and_advisory_summary(self):
        self.entry['url']='https://untrusted.invalid'
        value=reader.validate_index(self.index,self.files.__getitem__,self.origin)
        self.assertEqual(value['status'],'available')
        run=value['runs'][0]
        self.assertEqual(run['summary']['semantic_verdict'],'CLEAN')
        self.assertIn('/'+'c'*40+'/',run['url']);self.assertNotIn('untrusted',run['url'])

    def test_index_manifest_and_artifact_tampering_is_rejected(self):
        for key,value in [('outcome','fail'),('target',{}),('manifest_sha256','0'*64),('path','../escape')]:
            changed=copy.deepcopy(self.index);changed['runs'][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):reader.validate_index(changed,self.files.__getitem__,self.origin)
        path=self.entry['path']+'/report.json';self.files[path]+=b' '
        with self.assertRaises(ValueError):reader.validate_index(self.index,self.files.__getitem__,self.origin)

    def test_availability_states_do_not_collapse(self):
        self.assertEqual(reader.load(self.root)['status'],'not_configured')
        self.assertEqual(reader.validate_index({'schema_version':'fc.evidence-index.v1','runs':[]},lambda _:None)['status'],'no_records')
        core.save(self.root/'.conjectures/evidence-index.json',{'schema_version':'wrong'})
        self.assertEqual(reader.load(self.root)['status'],'invalid')
        core.save(self.root/'.conjectures/evidence-index.json',self.index)
        self.assertEqual(reader.load(self.root)['status'],'unavailable')

    def test_offline_cache_is_revalidated_without_network(self):
        destination={'repository':'owner/evidence','branch':'data'}
        cache=self.root/('evidence-'+rr.digest(rr.encode(destination))+'.json')
        files={k:v.decode() for k,v in self.files.items()};files['toolkit-index.json']=rr.encode(self.index).decode()
        core.save(cache,{'origin':self.origin,'retrieved_at':'2026-09-09T00:00:00Z','files':files})
        with patch.object(reader,'user_cache',return_value=self.root),patch.object(reader,'github',side_effect=AssertionError('network')):
            self.assertEqual(reader.load(None,destination,offline=True)['status'],'available')
            saved=rr.read_json(cache);saved['files'][self.entry['path']+'/report.json']='{}';core.save(cache,saved)
            self.assertEqual(reader.load(None,destination,offline=True)['status'],'invalid')
