"""Frozen proof tasks and a thin Harbor export; agents run in the external harness."""
import json
import re
import shutil
import tempfile
from pathlib import Path
from . import report as rr
from .core import Failure, save

SCHEMA='fc.proof-suite.v1'
IMAGE=r'[a-zA-Z0-9][a-zA-Z0-9._/:-]*@sha256:[a-f0-9]{64}'


def validate_suite(suite):
    rr.obj(suite,'schema_version source execution cases','proof suite')
    rr.require(suite['schema_version']==SCHEMA,'Unsupported proof suite')
    rr.obj(suite['source'],'repository commit','source')
    for key in ('repository','commit'):rr.text(suite['source'][key],key)
    rr.require(re.fullmatch(r'[\w.-]+/[\w.-]+',suite['source']['repository']) is not None,'Use source OWNER/REPO')
    rr.require(re.fullmatch('[a-f0-9]{40}',suite['source']['commit']) is not None,'Pin an exact source commit')
    execution=suite['execution']
    rr.obj(execution,'solver_image verifier_image toolkit_commit agent_seconds','execution')
    for key in ('solver_image','verifier_image'):
        rr.text(execution[key],key)
        rr.require(re.fullmatch(IMAGE,execution[key]) is not None,'Use a registry image pinned by sha256')
    rr.text(execution['toolkit_commit'],'toolkit_commit')
    rr.require(re.fullmatch('[a-f0-9]{40}',execution['toolkit_commit']) is not None,'Pin the trusted verifier toolkit commit')
    rr.require(type(execution['agent_seconds']) is int and 0<execution['agent_seconds']<=86400,'Agent budget must be 1–86400 seconds')
    rr.require(isinstance(suite['cases'],list) and 0<len(suite['cases'])<=100,'Select 1–100 exact targets')
    ids=set();targets=set()
    for case in suite['cases']:
        rr.obj(case,'id declaration exposure','case')
        rr.text(case['id'],'case ID')
        rr.require(re.fullmatch('[a-z0-9][a-z0-9-]{0,63}',case['id']) is not None,'Invalid case ID')
        rr.text(case['declaration'],'declaration');rr.text(case['exposure'],'known development exposure')
        rr.require(case['id'] not in ids and case['declaration'] not in targets,'Duplicate case or declaration')
        ids.add(case['id']);targets.add(case['declaration'])


def export(root,args):
    from . import catalog,proof
    suite=rr.read_json(args.suite);validate_suite(suite)
    data=catalog.load(root,args.catalog,url=getattr(args,'catalog_url',None))
    source=data.get('provenance',{}).get('source',{})
    if source.get('repository')!=suite['source']['repository'] or source.get('commit')!=suite['source']['commit']:
        raise Failure('catalog_binding_mismatch','Suite and selected catalog must name the same exact repository and revision.',4)
    selected={case['id']:catalog.select(data,case['declaration']) for case in suite['cases']}
    out=args.out.resolve()
    if out.exists():raise Failure('output_exists','Select a new export directory; existing tasks are preserved.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.fc-eval-',dir=out.parent) as temp:
        staging=Path(temp)/'tasks';staging.mkdir()
        for case in suite['cases']:
            task=staging/case['id'];task.mkdir()
            workspace=task/'environment/workspace'
            from .catalog_data import module_path
            problem=selected[case['id']]
            problem={**problem,'githubPath':problem.get('githubPath') or module_path(problem['module'])}
            generated=proof.generate(root,problem,suite['source']['repository'],suite['source']['commit'],Path(temp)/case['id'])
            shutil.copytree(generated,workspace)
            provenance=rr.read_json(workspace/'fc-provenance.json')
            proof.write_handoff(workspace,provenance)
            # An exported task must not carry operator run records or development caches.
            shutil.rmtree(workspace/'.conjectures',ignore_errors=True)
            (workspace/'Submission').mkdir(exist_ok=True)
            holes=bool(rr.read_json(workspace/'config.json').get('definition_names'))
            target={'schema_version':'fc.proof-task.v1','id':case['id'],'source':provenance['source'],
                    'toolkit_commit':suite['execution']['toolkit_commit'],'semantic_assessment_required':holes,
                    'suite_sha256':rr.digest(rr.encode(suite)),'exposure':case['exposure']}
            write_task(task,target,suite['execution'])
        save(staging/'suite.json',suite)
        files={p.relative_to(staging).as_posix():p.read_bytes() for p in staging.rglob('*') if p.is_file()}
        save(staging/'manifest.json',{'schema_version':'fc.proof-eval-export.v1','suite_sha256':rr.digest(rr.encode(suite)),
                                     'files':rr.descriptors(files)})
        staging.rename(out)
    return {'outcome':'pass','paths':{'tasks':str(out),'manifest':str(out/'manifest.json')},
            'message':f'Exported {len(suite["cases"])} frozen tasks. No agent was launched.',
            'next_action':'Run these tasks with your external Harbor harness and qualified images; preserve all trial records.'}


def write_task(task,target,execution):
    q=json.dumps
    (task/'instruction.md').write_text(
        f"Prove `{target['source']['declaration']}` in /app. Read /app/AGENTS.md and Challenge.lean.\n"
        'Edit Submission.lean and Lean files under Submission/. The harness grades those files\n'
        'in a separate trusted environment. Do not alter the target or grading configuration.\n'
        'Use lake build for development feedback. Do not publish or push your work.\n')
    (task/'task.toml').write_text(
        'schema_version = "1.4"\nartifacts = ["/app/Submission.lean", "/app/Submission"]\n'
        f'\n[task]\nname = "fc/{target["id"]}"\nversion = "{target["suite_sha256"][:16]}"\n'
        f'\n[metadata]\nsuite_sha256 = {q(target["suite_sha256"])}\nexposure = {q(target["exposure"])}\n'
        f'\n[agent]\ntimeout_sec = {execution["agent_seconds"]}\n'
        '\n[environment]\nos = "linux"\ncpus = 4\nmemory_mb = 8192\n'
        '\n[verifier]\ntimeout_sec = 3600\nenvironment_mode = "separate"\n'
        '\n[verifier.environment]\nos = "linux"\ncpus = 4\nmemory_mb = 8192\n')
    (task/'environment/Dockerfile').write_text(
        f'FROM {execution["solver_image"]}\nCOPY --chown=1000:1000 workspace /app\nWORKDIR /app\nUSER 1000:1000\n')
    tests=task/'tests';tests.mkdir()
    save(tests/'target.json',target)
    (tests/'Dockerfile').write_text(
        f'FROM {execution["verifier_image"]}\nCOPY --chown=1000:1000 . /tests\nUSER 1000:1000\nWORKDIR /app\n')
    (tests/'test.sh').write_text('#!/bin/sh\nset -eu\nexport PYTHONPATH=/opt/fc/toolkit\nexec python3 -m conjectures.eval_verifier --target /tests/target.json --submission /app --out /logs/verifier\n')


def summarize(directory):
    if not directory.is_dir():raise Failure('directory_missing','Select an existing harness output directory.')
    counts={key:0 for key in ('verified','rejected','assessment_required','error')};attempts=[]
    for path in sorted(directory.rglob('fc-result.json')):
        try:
            value=rr.read_json(path)
            rr.require(isinstance(value,dict),'Result must be an object')
            rr.require(value.get('schema_version')=='fc.proof-eval-result.v1','Unsupported result schema')
            rr.require(isinstance(value.get('status'),str) and value['status'] in counts,'Invalid result status')
            rr.text(value.get('task'),'task')
            digest=value.get('suite_sha256')
            # A verifier can fail before it reads the frozen task. Retain that error
            # without attributing it to a suite or counting it as a proof outcome.
            rr.require('suite_sha256' in value and (
                isinstance(digest,str) and re.fullmatch('[a-f0-9]{64}',digest) is not None
                or digest is None and value['status']=='error'),'Invalid suite digest')
        except (ValueError,OSError) as error:
            raise Failure('invalid_result',f'Invalid evaluation result {path}: {error}',3) from error
        counts[value['status']]+=1
        attempts.append({'path':str(path),'task':value['task'],'status':value['status'],'suite_sha256':value['suite_sha256']})
    return {'outcome':'pass','counts':counts,'attempts':attempts,
            'message':f'{len(attempts)} retained verifier attempts: '+', '.join(f'{n} {key}' for key,n in counts.items()),
            'coverage_gaps':['Attempts without verifier artifacts are not counted. Use the harness trial manifest for timeouts, cancellations, missing trials, and the full denominator.'],
            'next_action':'Compare against the frozen suite and harness trial records. This is not a pass@k estimate.'}
