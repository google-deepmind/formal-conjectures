"""Download and cache the published Lean catalog without parsing Lean syntax."""
import re
import urllib.request
import urllib.error
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin
from . import report as rr
from . import catalog_data
from .metadata import metadata_rows
from .core import Failure, save, now, user_cache

NATIVE_URL = 'https://google-deepmind.github.io/formal-conjectures/data/conjectures.json'
MANIFEST_URL = NATIVE_URL.replace('conjectures.json','catalog-manifest.json')
MAX_BYTES = 64*1024*1024
MAX_AGE = 24*60*60


def read_url(url, limit=MAX_BYTES):
    with urllib.request.urlopen(url,timeout=15) as response:
        raw=response.read(limit+1)
    if len(raw)>limit:raise ValueError('Catalog response is too large')
    return raw


def normalize(value):
    if not isinstance(value,dict) or not isinstance(value.get('problems'),list):
        raise ValueError('Expected the native schema-2 problems catalog')
    metadata_rows(value)
    return value


def result(data, origin, state):
    data=normalize(data)
    gaps=list(data.get('coverage_gaps',[]))
    if any(not p.get('statement') for p in data['problems']):
        gaps.append('This catalog omits statement text. Generate a complete native extract without excluding statements.')
    if not data.get('provenance'):
        gaps.append('The source revision is unavailable; this catalog cannot establish evidence applicability.')
    if state=='stale':gaps.append('Catalog refresh failed; showing the retained snapshot. Retry with --refresh when online.')
    if state in ('fresh','cached','offline','stale'):
        origin={**origin,'includes_local_changes':False}
    return {**data,'coverage_gaps':gaps,'catalog_origin':{**origin,'state':state}}


def load(root, path=None, *, refresh=False, offline=False):
    if path:
        path=Path(path)
        if not path.is_file():raise Failure('catalog_missing','Catalog file does not exist: '+str(path))
        return result(rr.read_json(path),{'path':str(path)},'explicit')
    cache=user_cache()/'catalog-cache.json'
    retained=None
    if cache.is_file():
        try:
            envelope=rr.read_json(cache)
            data=catalog_data.verify(envelope['descriptor'],envelope['raw'].encode())
            retained=(data,envelope['origin'])
            age=(datetime.now(timezone.utc)-datetime.fromisoformat(envelope['origin']['retrieved_at'])).total_seconds()
            if offline or not refresh and 0<=age<MAX_AGE:
                return result(*retained,'offline' if offline else 'cached')
        except (ValueError,KeyError,TypeError):pass
    if offline:
        if retained:return result(*retained,'offline')
        raise Failure('catalog_unavailable','No cached catalog. Run conjectures find erdos/92 while online first.',4)
    try:
        descriptor=catalog_data.parse(read_url(MANIFEST_URL,1024*1024))
        # The descriptor can only select the sibling catalog, never an arbitrary URL.
        if descriptor.get('catalog')!='conjectures.json':raise ValueError('Unexpected catalog filename')
        raw=read_url(urljoin(MANIFEST_URL,'conjectures.json'))
        data=catalog_data.verify(descriptor,raw)
        origin={'url':NATIVE_URL,'manifest_url':MANIFEST_URL,'retrieved_at':now(),'sha256':rr.digest(raw)}
        save(cache,{'schema_version':'fc.catalog-cache.v1','descriptor':descriptor,'raw':raw.decode(),'origin':origin})
        return result(data,origin,'fresh')
    except urllib.error.HTTPError as error:
        if error.code!=404:
            if retained:return result(*retained,'stale')
            raise Failure('catalog_unavailable',f'Catalog download failed (HTTP {error.code}). Retry with --refresh.',4) from error
        if retained:return result(*retained,'stale')
        raise Failure('catalog_not_published','The full catalog is not published yet. Browsing requires FC #5375 to merge and deploy. Use --catalog FILE only for an explicitly generated native extract.',4) from error
    except (OSError,ValueError,TypeError) as error:
        if retained:return result(*retained,'stale')
        raise Failure('catalog_unavailable','Cannot obtain a validated catalog: '+str(error)+'. Retry with --refresh.',4) from error


def matches(catalog, query):
    words = query.casefold().split()
    shortcut = re.fullmatch(r'erdos/(\d+)',query.casefold())
    if shortcut:
        return [p for p in catalog['problems'] if p['module'] in
                ('FormalConjectures.ErdosProblems.«'+shortcut[1]+'»','FormalConjectures.ErdosProblems.'+shortcut[1])]
    exact = [p for p in catalog['problems'] if p['theorem'] == query]
    if exact: return exact
    return [p for p in catalog['problems'] if all(w in ' '.join(str(p.get(k,'')) for k in
            ('theorem','module','statement','docstring','subjects')).casefold() for w in words)]

def select(catalog, query):
    found = matches(catalog,query)
    if len(found)!=1:
        raise Failure('ambiguous_target' if found else 'unknown_target',
                      'Choose an exact declaration: '+', '.join(p['theorem'] for p in found[:20]))
    return found[0]


def attach_evidence(problems, root, cfg, source=None, *, offline=False):
    from .evidence_reader import load as load_evidence
    from .projections import evidence_for
    index=load_evidence(root,cfg.get('evidence'),offline=offline)
    source=source or {}
    return [{**p,'evidence':evidence_for(p,index,source.get('commit'),source.get('repository')),
             'evidence_availability':index['status'], 'evidence_message':index.get('message'),
             'evidence_observed_at':index.get('observed_at')} for p in problems]
