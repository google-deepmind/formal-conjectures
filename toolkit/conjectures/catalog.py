"""Consume the published native extraction without parsing Lean syntax."""
import re
import urllib.request
from pathlib import Path
from . import report as rr
from .metadata import metadata_rows
from .core import Failure, command, git, save, now
URL = 'https://google-deepmind.github.io/formal-conjectures/data/conjectures.json'

def load(root, path=None):
    candidates = [Path(path)] if path else [root/'.conjectures/catalog.json', root/'site/data/conjectures.json']
    for candidate in candidates:
        if candidate.is_file():
            value = rr.read_json(candidate); break
    else:
        with urllib.request.urlopen(URL, timeout=30) as response:
            raw = response.read(32*1024*1024+1)
        if len(raw)>32*1024*1024: raise Failure('invalid_catalog','Catalog too large')
        value = rr.parse(raw)
        save(root/'.conjectures/catalog.json',value)
        save(root/'.conjectures/catalog-origin.json',{'url':URL,'retrieved_at':now(),'sha256':rr.digest(raw),
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
