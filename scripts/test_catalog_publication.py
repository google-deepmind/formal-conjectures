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
        raw=(out/'catalog.json').read_bytes();descriptor=(out/'catalog-manifest.json').read_bytes()
        publish_catalog.prepare(self.root,'owner/fc',fixture(),out)
        self.assertEqual(raw,(out/'catalog.json').read_bytes());self.assertEqual(descriptor,(out/'catalog-manifest.json').read_bytes())
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
        raw=(out/'catalog.json').read_bytes();descriptor=(out/'catalog-manifest.json').read_bytes()
        with patch.object(download_catalog,'urlopen',side_effect=[BytesIO(descriptor),BytesIO(raw)]):
            download_catalog.download('https://example.org/data/catalog-manifest.json',self.root/'preview')
        self.assertEqual((self.root/'preview/conjectures.json').read_bytes(),raw)
        self.assertEqual((self.root/'preview/catalog-manifest.json').read_bytes(),descriptor)

    def test_descriptor_cannot_redirect_to_another_origin(self):
        from io import BytesIO
        with patch.object(download_catalog,'urlopen',return_value=BytesIO(b'{"catalog":"https://other.example/data"}')) as network:
            with self.assertRaises(ValueError):download_catalog.download('https://example.org/data/catalog-manifest.json',self.root/'preview')
        self.assertEqual(network.call_count,1)
