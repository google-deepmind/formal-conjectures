"""Publication rejects incomplete data and preserves exact native observations."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import publish_catalog
import download_catalog
from conjectures import catalog_data


def fixture():
    module='FormalConjectures.ErdosProblems.«92»'
    return {'schemaVersion':2,'problems':[
        {'theorem':'Erdos92.'+variant,'module':module,'statement':'∀ n : ℕ, n = n',
         'category':'research solved','subjects':['11'],'docstring':'Fixture',
         'answerKinds':['Prop'],'hasSorryFreeProof':False,
         'formalProofs':[{'kind':'lean4','link':'https://example.org/proof','conditions':['Unproved hypothesis']}]} for variant in ('strong','weak')],
        'moduleDocstrings':{module:'Source: https://example.org/problem'}}


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        def git(*args):return subprocess.check_output(['git','-C',str(self.root),*args],stderr=subprocess.DEVNULL).decode().strip()
        self.git=git;git('init');git('config','user.email','fixture@example.invalid');git('config','user.name','Fixture')
        (self.root/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n');(self.root/'lake-manifest.json').write_text('{}')
        git('add','.');git('commit','-m','Pinned inputs')

    def test_repeat_publication_has_identical_bytes_and_retains_variants(self):
        out=self.root/'out'
        data=publish_catalog.prepare(self.root,'owner/fc',fixture(),out)
        raw=(out/'conjectures.json').read_bytes();descriptor=(out/'catalog-manifest.json').read_bytes()
        publish_catalog.prepare(self.root,'owner/fc',fixture(),out)
        self.assertEqual(raw,(out/'conjectures.json').read_bytes());self.assertEqual(descriptor,(out/'catalog-manifest.json').read_bytes())
        self.assertEqual(catalog_data.verify(json.loads(descriptor),raw),data)
        self.assertEqual(data['problems'],fixture()['problems'])
        self.assertEqual(data['provenance']['source']['commit'],self.git('rev-parse','HEAD'))

    def test_incomplete_projection_and_dirty_source_cannot_publish(self):
        data=fixture();del data['problems'][0]['statement']
        with self.assertRaises(ValueError):publish_catalog.prepare(self.root,'owner/fc',data,self.root/'out')
        (self.root/'lean-toolchain').write_text('changed')
        with self.assertRaises(ValueError):publish_catalog.prepare(self.root,'owner/fc',fixture(),self.root/'out')

    def test_preview_keeps_original_bytes_and_provenance(self):
        from io import BytesIO
        out=self.root/'out';publish_catalog.prepare(self.root,'owner/fc',fixture(),out)
        raw=(out/'conjectures.json').read_bytes();descriptor=(out/'catalog-manifest.json').read_bytes()
        index=catalog_data.encode({'schema_version':'fc.website-modules.v1','catalog_sha256':json.loads(descriptor)['sha256'],
            'modules':[{'name':'FormalConjecturesUtil.Example','url':'/FormalConjecturesUtil/Example/'}]})
        with patch.object(download_catalog,'urlopen',side_effect=[BytesIO(descriptor),BytesIO(raw),BytesIO(index)]):
            download_catalog.download('https://example.org/data/catalog-manifest.json',self.root/'preview')
        self.assertEqual((self.root/'preview/conjectures.json').read_bytes(),raw)
        self.assertEqual((self.root/'preview/catalog-manifest.json').read_bytes(),descriptor)
        self.assertEqual((self.root/'preview/verso-modules.json').read_bytes(),index)
        with patch.object(download_catalog,'urlopen',side_effect=[BytesIO(descriptor),BytesIO(raw),BytesIO(index.replace(json.loads(descriptor)['sha256'].encode(),b'c'*64))]):
            with self.assertRaisesRegex(ValueError,'another catalog'):
                download_catalog.download('https://example.org/data/catalog-manifest.json',self.root/'invalid-preview')
        self.assertFalse((self.root/'invalid-preview').exists())

    def test_descriptor_cannot_redirect_to_another_origin(self):
        from io import BytesIO
        with patch.object(download_catalog,'urlopen',return_value=BytesIO(b'{"catalog":"https://other.example/data"}')) as network:
            with self.assertRaises(ValueError):download_catalog.download('https://example.org/data/catalog-manifest.json',self.root/'preview')
        self.assertEqual(network.call_count,1)

    def test_uncommitted_shared_imports_cannot_claim_a_source_commit(self):
        for name in ('FormalConjecturesUtil.lean', 'FormalConjecturesForMathlib.lean'):
            file=self.root/name
            for state in ('untracked', 'modified', 'staged', 'deleted'):
                with self.subTest(file=name,state=state):
                    file.write_text('import Modified')
                    if state!='untracked':
                        self.git('add',name);self.git('commit','-m','Pin aggregate')
                        if state=='deleted':file.unlink()
                        else:file.write_text('import Changed')
                        if state=='staged':self.git('add',name)
                    with self.assertRaisesRegex(ValueError,'uncommitted changes'):
                        publish_catalog.prepare(self.root,'owner/fc',fixture(),self.root/'out')
                    self.assertFalse((self.root/'out').exists())
                    if state=='untracked':file.unlink()
                    else:self.git('reset','--hard','HEAD^')
        publish_catalog.prepare(self.root,'owner/fc',fixture(),self.root/'out')
