"""The published data contract and cache must work without a checkout or credentials."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from conjectures import catalog, catalog_data, core


def native():
    module='FormalConjectures.ErdosProblems.«92»'
    return {'schemaVersion':2,'problems':[{'theorem':'Erdos92.strong','module':module,
        'statement':'∀ n : ℕ, n = n','category':'research solved','docstring':'A fixture.',
        'subjects':['11'],'answerKinds':[],'hasSorryFreeProof':False}],
        'moduleDocstrings':{module:'Source https://example.org/92'},
        'provenance':{'source':{'repository':'owner/fc','commit':'a'*40},
        'extractor':{'repository':'owner/fc','commit':'a'*40},
        'lean_toolchain':'leanprover/lean4:v4.33.1','dependencies_sha256':'b'*64,
        'scope':'FormalConjectures','answer_mode':'postpone'}}


class CatalogTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.cache=patch.object(catalog,'user_cache',return_value=self.root);self.cache.start();self.addCleanup(self.cache.stop)

    def fetch(self,data=None):
        data=data or native();raw=catalog_data.encode(data)
        descriptor=catalog_data.encode(catalog_data.manifest(data,raw))
        with patch.object(catalog,'read_url',side_effect=[descriptor,raw]) as network:
            value=catalog.load(None,refresh=True)
        self.assertEqual(network.call_args_list[0].args[0],catalog.MANIFEST_URL)
        return value

    def test_full_catalog_replaces_legacy_cache_and_refreshes_atomically(self):
        core.save(self.root/'catalog.json',{'conjectures':[{'theorem':'Old','module':'Old'}]})
        first=self.fetch();self.assertIn('∀ n',first['problems'][0]['statement'])
        self.assertEqual(first['catalog_origin']['state'],'fresh')
        with patch.object(catalog,'read_url',side_effect=AssertionError('unexpected network')):
            self.assertEqual(catalog.load(None)['catalog_origin']['state'],'cached')
            self.assertEqual(catalog.load(None,offline=True)['catalog_origin']['state'],'offline')
        updated=native();updated['provenance']['source']['commit']='c'*40
        self.assertEqual(self.fetch(updated)['provenance']['source']['commit'],'c'*40)

    def test_404_does_not_download_legacy_projection_or_fork_data(self):
        core.save(self.root/'catalog.json',{'conjectures':[]})
        error=catalog.urllib.error.HTTPError(catalog.MANIFEST_URL,404,'missing',{},None)
        with patch.object(catalog,'read_url',side_effect=error) as network:
            with self.assertRaises(core.Failure) as failure:catalog.load(None)
        self.assertEqual(failure.exception.reason,'catalog_not_published')
        self.assertEqual(failure.exception.code,4);self.assertEqual(network.call_count,1)

    def test_failed_refresh_preserves_valid_snapshot_with_explicit_staleness(self):
        self.fetch()
        with patch.object(catalog,'read_url',side_effect=OSError('offline')):
            value=catalog.load(None,refresh=True)
        self.assertEqual(value['catalog_origin']['state'],'stale')
        self.assertTrue(any('refresh failed' in gap for gap in value['coverage_gaps']))
        self.assertEqual(catalog.load(None,offline=True)['provenance'],native()['provenance'])

    def test_expired_cache_fetches_new_catalog(self):
        self.fetch();path=self.root/'catalog-cache.json';value=json.loads(path.read_text())
        value['origin']['retrieved_at']='2000-01-01T00:00:00+00:00';core.save(path,value)
        with patch.object(catalog,'read_url',side_effect=OSError('offline')) as network:
            self.assertEqual(catalog.load(None)['catalog_origin']['state'],'stale')
            network.assert_called_once()

    def test_digest_and_missing_statements_fail_closed(self):
        data=native();raw=catalog_data.encode(data);descriptor=catalog_data.manifest(data,raw)
        with self.assertRaises(ValueError):catalog_data.verify(descriptor,raw+b' ')
        missing=copy.deepcopy(data);del missing['problems'][0]['statement']
        with self.assertRaises(ValueError):catalog_data.complete(missing)
        with patch.object(catalog,'read_url',side_effect=[catalog_data.encode(descriptor),raw+b' ']):
            with self.assertRaises(core.Failure):catalog.load(None)
        self.assertFalse((self.root/'catalog-cache.json').exists())

    def test_pinned_source_url_and_quoted_module_path(self):
        data=native();url=catalog_data.source_url(data['provenance']['source'],data['problems'][0]['module'])
        self.assertEqual(url,'https://github.com/owner/fc/blob/'+'a'*40+'/FormalConjectures/ErdosProblems/92.lean')
        self.assertEqual(catalog_data.module_path('FormalConjectures.Example.«a.b»'),'FormalConjectures/Example/a.b.lean')
