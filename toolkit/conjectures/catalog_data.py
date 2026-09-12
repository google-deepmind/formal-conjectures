"""Static catalog publication contract shared by the CLI and build scripts."""
import hashlib
import json
import re
from urllib.parse import quote
from .metadata import metadata_rows

MANIFEST_SCHEMA = 'fc.catalog.v1'

# Shared Lean inputs for catalog publication and Verso snapshot checks.
SOURCE_INPUTS = (
    'FormalConjectures', 'FormalConjecturesUtil', 'FormalConjecturesForMathlib',
    'FormalConjecturesUtil.lean', 'FormalConjecturesForMathlib.lean',
    'lakefile.toml', 'lean-toolchain', 'lake-manifest.json',
)


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
    if not rows or not isinstance(data.get('moduleDocstrings'),dict) or not all(isinstance(v,str) for v in data['moduleDocstrings'].values()):
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
        if row['category'] not in ('research open','research solved','textbook','test','API'):
            raise ValueError('Invalid category')
        if not isinstance(row.get('subjects'),list) or not all(isinstance(v,str) and re.fullmatch(r'[0-9]{1,2}',v) for v in row['subjects']):
            raise ValueError('Invalid or missing subjects')
        if 'docstring' not in row or (row['docstring'] is not None and not isinstance(row['docstring'],str)):
            raise ValueError('Invalid or missing docstring')
        if not isinstance(row.get('answerKinds'),list) or not all(v in ('Prop','non-Prop') for v in row['answerKinds']):
            raise ValueError('Invalid or missing answerKinds')
        if not isinstance(row.get('hasSorryFreeProof'),bool):
            raise ValueError('Invalid or missing hasSorryFreeProof')
        if 'subsets' in row and (not isinstance(row['subsets'],list) or not all(isinstance(v,str) and v for v in row['subsets'])):
            raise ValueError('Invalid subsets')
        for field in ('fileFirstAdded','fileLastModified'):
            if row.get(field) is not None and not isinstance(row[field],str):
                raise ValueError('Invalid '+field)
        if any(not condition for proof in row.get('formalProofs',[]) for condition in proof['conditions']):
            raise ValueError('Empty proof condition')
        if row['module'] not in data['moduleDocstrings']:
            raise ValueError('Full catalog is missing module sources: '+row['module'])
    provenance=data.get('provenance',{})
    if not isinstance(provenance,dict):raise ValueError('Invalid catalog provenance')
    source=provenance.get('source',{})
    if not isinstance(source,dict):raise ValueError('Invalid source revision')
    if not isinstance(source.get('repository'),str) or not re.fullmatch(r'[\w.-]+/[\w.-]+',source['repository'],re.ASCII) or not isinstance(source.get('commit'),str) or not re.fullmatch(r'[0-9a-f]{40}',source['commit']):
        raise ValueError('Catalog requires an exact GitHub source revision')
    if provenance.get('scope')!='FormalConjectures' or provenance.get('answer_mode')!='postpone':
        raise ValueError('Catalog must record full extraction with answer postponement')
    if not isinstance(provenance.get('lean_toolchain'),str) or not provenance['lean_toolchain'] or not isinstance(provenance.get('dependencies_sha256'),str) or not re.fullmatch(r'[0-9a-f]{64}',provenance['dependencies_sha256']):
        raise ValueError('Catalog requires toolchain and dependency provenance')
    extractor=provenance.get('extractor',{})
    if not isinstance(extractor,dict) or extractor.get('repository')!=source['repository'] or not isinstance(extractor.get('commit'),str) or not re.fullmatch(r'[0-9a-f]{40}',extractor['commit']) or extractor.get('path')!='scripts/extract_names.lean':
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
