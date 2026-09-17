"""Prepare every trusted workspace of a frozen evaluation suite once, at image build time.

The verifier image then checks submissions without fetching sources, packages or caches.
Workspaces share one pinned package directory; each case retains its own export provenance.
"""
import argparse
import json
import re
from pathlib import Path
from . import report as rr
from .core import Failure, command, git, save
from .ui import stage

CORE = 'fc.proof-suite-core.v1'
CASE = 'fc.proof-suite-case.v1'
ROOT = Path('/opt/fc-suite')


def validate_core(value):
    rr.obj(value,'schema_version source cases','suite core')
    rr.require(value['schema_version']==CORE,'Unsupported suite core')
    rr.obj(value['source'],'repository commit','source')
    rr.require(re.fullmatch(r'[\w.-]+/[\w.-]+',value['source']['repository']) is not None,'Use source OWNER/REPO')
    rr.require(re.fullmatch('[a-f0-9]{40}',value['source']['commit']) is not None,'Pin an exact source commit')
    rr.require(isinstance(value['cases'],list) and 0<len(value['cases'])<=100,'Select 1–100 exact targets')
    ids=set();targets=set()
    for case in value['cases']:
        rr.obj(case,'id declaration path','case')
        rr.require(isinstance(case['id'],str) and re.fullmatch('[a-z0-9][a-z0-9-]{0,63}',case['id']) is not None,'Invalid case ID')
        rr.text(case['declaration'],'declaration');rr.relative(case['path'])
        rr.require(case['path'].endswith('.lean'),'Case path must name a Lean file')
        rr.require(case['id'] not in ids and case['declaration'] not in targets,'Duplicate case or declaration')
        ids.add(case['id']);targets.add(case['declaration'])


def core(suite):
    """The image-bound part of a suite: exact source and targets, without images or budgets."""
    value={'schema_version':CORE,'source':dict(suite['source']),
           'cases':[{key:case[key] for key in ('id','declaration','path')} for case in suite['cases']]}
    validate_core(value)
    return value


def core_digest(value):
    return rr.digest(rr.encode(value))


def packages(workspace):
    manifest=rr.read_json(workspace/'lake-manifest.json')
    return sorted((p.get('name'),p.get('url'),p.get('rev')) for p in manifest.get('packages',[]))


def prepare(core_path,out,toolkit,generator):
    from . import proof
    value=rr.read_json(core_path);validate_core(value);digest=core_digest(value)
    out=out.resolve()
    if out.exists() and any(out.iterdir()):raise Failure('output_exists','Suite directory is not empty.',3)
    shared=out/'packages';shared.mkdir(parents=True)
    repository=value['source']['repository'];commit=value['source']['commit']
    toolkit_commit=git(toolkit,'rev-parse','HEAD').decode().strip()
    workspaces={}
    with proof.prepared_source(None,repository,commit) as source:
        for case in value['cases']:
            stage('Exporting '+case['declaration'])
            problem={'theorem':case['declaration'],'githubPath':case['path'],'module':''}
            workspaces[case['id']]=proof.generate(None,problem,repository,commit,out/'cases'/case['id'],generator,source=source)
    pins={tuple(packages(ws)) for ws in workspaces.values()}
    if len(pins)!=1:raise Failure('package_pins_differ','Suite cases require different package revisions.',3)
    for index,(case_id,workspace) in enumerate(workspaces.items()):
        (workspace/'.lake').mkdir(exist_ok=True)
        (workspace/'.lake/packages').symlink_to(shared)
        stage('Resolving shared pinned dependencies for '+case_id)
        command(['lake','update'],cwd=workspace,timeout=1800)
        if index==0:command(['lake','exe','cache','get'],cwd=workspace,timeout=1800)
        stage('Building the trusted Challenge for '+case_id)
        command(['lake','build','Challenge'],cwd=workspace,timeout=3600)
        if tuple(packages(workspace))!=next(iter(pins)):
            raise Failure('package_pins_changed','Dependency resolution changed a pinned package.',3)
        provenance=rr.read_json(workspace/'fc-provenance.json')
        config=rr.read_json(workspace/'config.json')
        save(out/'cases'/case_id/'target.json',{'schema_version':CASE,'id':case_id,'core_sha256':digest,
             'source':provenance['source'],'toolkit_commit':toolkit_commit,
             'semantic_assessment_required':bool(config.get('definition_names'))})
    save(out/'suite-core.json',value)
    return {'outcome':'pass','core_sha256':digest,'cases':list(workspaces)}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=['prepare','core'])
    p.add_argument('--core',type=Path);p.add_argument('--suite',type=Path)
    p.add_argument('--out',type=Path,default=ROOT)
    p.add_argument('--toolkit',type=Path,default=Path('/opt/fc'))
    p.add_argument('--generator',type=Path,default=Path('/opt/fc-tools/generator'))
    args=p.parse_args()
    if args.command=='core':
        print(json.dumps(core(rr.read_json(args.suite)),indent=2))
        return 0
    print(json.dumps(prepare(args.core,args.out,args.toolkit.resolve(),args.generator.resolve())))
    return 0


if __name__=='__main__':raise SystemExit(main())
