"""Static catalog publication contract shared by the CLI and build scripts."""
import hashlib
import json
import re
from urllib.parse import quote
from .metadata import metadata_rows

MANIFEST_SCHEMA = 'fc.catalog.v1'


def repository_name(value):
    """Compare equivalent GitHub repository locators, retaining no branch identity."""
    match=re.fullmatch(r'(?:https://github.com/)?([\w.-]+/[\w.-]+?)(?:\.git)?',value or '')
    return match[1].casefold() if match else None


def encode(value):
    return (json.dumps(value, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(',', ':'))+'\n').encode()


def parse(raw):
    def unique(pairs):
        value={}
        for key,item in pairs:
            if key in value:raise ValueError('Duplicate JSON member: '+key)
            value[key]=item
        return value
    def invalid(value):raise ValueError('Non-finite JSON number: '+value)
    return json.loads(raw,object_pairs_hook=unique,parse_constant=invalid)


def module_path(module):
    """Decode Lean-printed name components, without interpreting Lean source."""
    parts=[];buf='';quoted=False
    for ch in module:
        if ch=='«':quoted=True
        elif ch=='»':quoted=False
        elif ch=='.' and not quoted:parts.append(buf);buf=''
        else:buf+=ch
    parts.append(buf)
    if quoted or parts[0]!='FormalConjectures' or any(not p or '/' in p or p in ('.','..') for p in parts):
        raise ValueError('Invalid problem module')
    return '/'.join(parts)+'.lean'


def complete(data):
    rows=metadata_rows(data)
    if not rows or not isinstance(data.get('moduleDocstrings'),dict):
        raise ValueError('A full catalog requires problems and module docstrings')
    seen=set()
    for row in rows:
        for key in ('theorem','module','statement','category'):
            if not isinstance(row.get(key),str) or not row[key].strip():
                raise ValueError('Full catalog is missing '+key)
        module_path(row['module'])
        key=(row['module'],row['theorem'])
        if key in seen:raise ValueError('Duplicate declaration identity')
        seen.add(key)
        if 'docstring' not in row or not isinstance(row.get('answerKinds'),list) or not isinstance(row.get('hasSorryFreeProof'),bool):
            raise ValueError('Full catalog is missing native observations')
        if row['module'] not in data['moduleDocstrings']:
            raise ValueError('Full catalog is missing module sources: '+row['module'])
    provenance=data.get('provenance',{})
    source=provenance.get('source',{})
    if not re.fullmatch(r'[\w.-]+/[\w.-]+',source.get('repository','')) or not re.fullmatch(r'[0-9a-f]{40}',source.get('commit','')):
        raise ValueError('Catalog requires an exact GitHub source revision')
    if provenance.get('scope')!='FormalConjectures' or provenance.get('answer_mode')!='postpone':
        raise ValueError('Catalog must record full extraction with answer postponement')
    if not provenance.get('lean_toolchain') or not re.fullmatch(r'[0-9a-f]{64}',provenance.get('dependencies_sha256','')):
        raise ValueError('Catalog requires toolchain and dependency provenance')
    extractor=provenance.get('extractor',{})
    if extractor.get('repository')!=source['repository'] or not re.fullmatch(r'[0-9a-f]{40}',extractor.get('commit','')):
        raise ValueError('Catalog requires an exact extractor revision')
    return data


def manifest(data, raw):
    complete(data)
    return {'schema_version':MANIFEST_SCHEMA,'catalog':'conjectures.json',
            'schema':'schemas/catalog-v2.schema.json',
            'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),
            'problem_count':len(data['problems']),'provenance':data['provenance']}


def verify(descriptor, raw):
    if not isinstance(descriptor,dict) or descriptor.get('schema_version')!=MANIFEST_SCHEMA:
        raise ValueError('Unsupported catalog descriptor')
    if descriptor.get('catalog')!='conjectures.json':raise ValueError('Unexpected catalog filename')
    if len(raw)!=descriptor.get('bytes') or hashlib.sha256(raw).hexdigest()!=descriptor.get('sha256'):
        raise ValueError('Catalog digest or size differs from its descriptor')
    data=complete(parse(raw))
    if data['provenance']!=descriptor.get('provenance') or len(data['problems'])!=descriptor.get('problem_count'):
        raise ValueError('Catalog provenance or count differs from its descriptor')
    return data


def source_url(source, module):
    return f"https://github.com/{source['repository']}/blob/{source['commit']}/{quote(module_path(module),safe='/')}"
