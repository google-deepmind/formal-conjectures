"""Consume the published native extraction without parsing Lean syntax."""
import re
import urllib.request
import urllib.error
from pathlib import Path
from . import report as rr
from .metadata import metadata_rows
from .core import Failure, command, git, save, now, user_cache
URL = 'https://google-deepmind.github.io/formal-conjectures/data/conjectures.json'
NATIVE_URL = 'https://google-deepmind.github.io/formal-conjectures/data/catalog.json'

def load(root, path=None):
    cache = root/'.conjectures' if root else user_cache()
    candidates = [Path(path)] if path else [cache/'catalog.json', *([root/'site/data/catalog.json', root/'site/data/conjectures.json'] if root else [])]
    for candidate in candidates:
        if candidate.is_file():
            value = rr.read_json(candidate); break
    else:
        if path:
            raise Failure('catalog_missing', 'Catalog file does not exist: '+str(path))
        url = NATIVE_URL
        try:
            response = urllib.request.urlopen(url, timeout=30)
        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise
            url = URL
            response = urllib.request.urlopen(url, timeout=30)
        with response:
            raw = response.read(32*1024*1024+1)
        if len(raw)>32*1024*1024: raise Failure('invalid_catalog','Catalog too large')
        value = rr.parse(raw)
        save(cache/'catalog.json',value)
        save(cache/'catalog-origin.json',{'url':url,'retrieved_at':now(),'sha256':rr.digest(raw),
             'applicability':'Published catalog; init resolves and checks the source commit separately.'})
    if 'conjectures' in value:
        # The live website projection omits statement text and proof-term observations.
        # Preserve that absence rather than manufacturing complete native metadata.
        return {'schemaVersion': 2, 'projection': 'website', 'problems': [
            {**p, 'subjects': [s['code'] if isinstance(s,dict) else s for s in p.get('subjects',[])]}
            for p in value['conjectures']], 'coverage_gaps': ['Published website projection omits statement text; supply --catalog with the full native extract.']}
    if value.get('schemaVersion') != 2 or not isinstance(value.get('problems'),list):
        raise Failure('unsupported_catalog','Expected native extraction schemaVersion 2')
    metadata_rows(value)
    return value

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


def attach_evidence(problems, root, cfg):
    import importlib.util
    if importlib.util.find_spec("conjectures.projections") is None:
        return [{**p,"evidence":[]} for p in problems]
    from .projections import evidence_for
    from urllib.parse import quote
    index=None
    path=root/'.conjectures/evidence-index.json' if root else None
    if path and path.is_file():index=rr.read_json(path)
    elif cfg.get('evidence'):
        destination=cfg['evidence'];repo=destination.get('repository','');branch=destination.get('branch','')
        if re.fullmatch(r'[\w.-]+/[\w.-]+',repo) and branch:
            try:
                url=f'https://raw.githubusercontent.com/{repo}/{quote(branch,safe="")}/toolkit-index.json'
                with urllib.request.urlopen(url,timeout=10) as response:raw=response.read(8*1024*1024+1)
                if len(raw)<=8*1024*1024:index=rr.parse(raw)
            except (OSError,ValueError):pass
    if not isinstance(index,dict) or index.get('schema_version')!='fc.evidence-index.v1':index={'runs':[]}
    revision=None
    if root:
        try:
            if not git(root,'status','--porcelain').strip():revision=git(root,'rev-parse','HEAD').decode().strip()
        except Failure:pass
    return [{**p,'evidence':evidence_for(p,index,revision)} for p in problems]
