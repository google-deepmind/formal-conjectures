"""Frozen proof suites exported as Harbor tasks; agents run in the external harness.

A suite is bound to two prebuilt images. The verifier image carries every prepared workspace
and pinned package for the suite core, so verification needs no network. The solver image
carries the same packages, so an agent's budget is not spent acquiring dependencies.
"""
import json
import re
import shutil
import tempfile
from pathlib import Path
from . import report as rr, eval_suite
from .core import Failure, command, save

SCHEMA='fc.proof-suite.v2'
IMAGE=r'[a-zA-Z0-9][a-zA-Z0-9._/:-]*@sha256:[a-f0-9]{64}'
TEST_SCRIPT=('#!/bin/sh\nset -eu\nexport PYTHONPATH=/opt/fc/toolkit\n'
             'exec python3 -m conjectures.eval_verifier --submission /app --out /logs/verifier\n')


def validate_suite(suite):
    rr.obj(suite,'schema_version source execution cases','proof suite')
    rr.require(suite['schema_version']==SCHEMA,'Unsupported proof suite')
    execution=suite['execution']
    rr.obj(execution,'solver_image verifier_image toolkit_commit agent_seconds','execution')
    for key in ('solver_image','verifier_image'):
        rr.text(execution[key],key)
        rr.require(re.fullmatch(IMAGE,execution[key]) is not None,'Use a registry image pinned by sha256')
    rr.text(execution['toolkit_commit'],'toolkit_commit')
    rr.require(re.fullmatch('[a-f0-9]{40}',execution['toolkit_commit']) is not None,'Pin the trusted verifier toolkit commit')
    rr.require(type(execution['agent_seconds']) is int and 0<execution['agent_seconds']<=86400,'Agent budget must be 1–86400 seconds')
    rr.require(isinstance(suite['cases'],list),'Select exact targets')
    for case in suite['cases']:
        rr.obj(case,'id declaration path exposure','case')
        rr.text(case['exposure'],'known development exposure')
    eval_suite.core(suite)


def image_files(image,paths,destination):
    """Copy prepared suite files out of the verifier image; nothing in the image is executed."""
    container=command(['docker','create','--pull','missing',image],timeout=3600).decode().strip()
    try:
        for path in paths:command(['docker','cp',f'{container}:{path}',str(destination)],timeout=1800)
    finally:command(['docker','rm',container])


def export(root,args):
    from . import proof
    suite=rr.read_json(args.suite);validate_suite(suite)
    core=eval_suite.core(suite);core_sha256=eval_suite.core_digest(core);suite_sha256=rr.digest(rr.encode(suite))
    out=args.out.resolve()
    if out.exists():raise Failure('output_exists','Select a new export directory; existing tasks are preserved.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.fc-eval-',dir=out.parent) as temp:
        staging=Path(temp)/'tasks';staging.mkdir()
        prepared=Path(temp)/'prepared';prepared.mkdir()
        # Solver workspaces come from the verifier image, so both sides grade the same Challenge.
        image_files(suite['execution']['verifier_image'],[f'{eval_suite.ROOT}/suite-core.json',f'{eval_suite.ROOT}/cases'],prepared)
        if rr.read_json(prepared/'suite-core.json')!=core:
            raise Failure('suite_image_mismatch','The verifier image was prepared for a different suite core.',4)
        for case in suite['cases']:
            baked=prepared/'cases'/case['id']
            target=rr.read_json(baked/'target.json')
            if target.get('core_sha256')!=core_sha256 or target.get('toolkit_commit')!=suite['execution']['toolkit_commit']:
                raise Failure('suite_image_mismatch','A prepared case does not match the frozen suite.',4)
            task=staging/case['id'];workspace=task/'environment/workspace'
            shutil.copytree(baked/'workspace',workspace,ignore=shutil.ignore_patterns('.lake'))
            proof.write_handoff(workspace,rr.read_json(workspace/'fc-provenance.json'))
            (workspace/'Submission').mkdir(exist_ok=True)
            write_task(task,{'id':case['id'],'source':target['source'],'suite_sha256':suite_sha256,
                             'core_sha256':core_sha256,'exposure':case['exposure'],
                             'semantic_assessment_required':target['semantic_assessment_required']},suite['execution'])
        save(staging/'suite.json',suite)
        files={p.relative_to(staging).as_posix():p.read_bytes() for p in staging.rglob('*') if p.is_file()}
        save(staging/'manifest.json',{'schema_version':'fc.proof-eval-export.v2','suite_sha256':suite_sha256,
                                     'core_sha256':core_sha256,'files':rr.descriptors(files)})
        staging.rename(out)
    return {'outcome':'pass','paths':{'tasks':str(out),'manifest':str(out/'manifest.json')},
            'message':f'Exported {len(suite["cases"])} frozen tasks. No agent was launched.',
            'next_action':'Run these tasks with your external Harbor harness; preserve all trial records.'}


def write_task(task,target,execution):
    q=json.dumps
    (task/'instruction.md').write_text(
        f"Prove `{target['source']['declaration']}` in /app. Read /app/AGENTS.md and Challenge.lean.\n"
        'Edit Submission.lean and Lean files under Submission/. The harness grades those files\n'
        'in a separate trusted environment. Do not alter the target or grading configuration.\n'
        'Dependencies are prebuilt: use lake build for feedback and do not run lake update.\n'
        'Do not publish or push your work.\n')
    (task/'task.toml').write_text(
        'schema_version = "1.4"\nartifacts = ["/app/Submission.lean", "/app/Submission"]\n'
        f'\n[task]\nname = "fc/{target["id"]}"\nversion = "{target["suite_sha256"][:16]}"\n'
        f'\n[metadata]\nsuite_sha256 = {q(target["suite_sha256"])}\ncore_sha256 = {q(target["core_sha256"])}\n'
        f'exposure = {q(target["exposure"])}\nsemantic_assessment_required = {str(target["semantic_assessment_required"]).lower()}\n'
        f'\n[agent]\ntimeout_sec = {execution["agent_seconds"]}\n'
        '\n[environment]\nos = "linux"\ncpus = 4\nmemory_mb = 8192\nbuild_timeout_sec = 1800\n'
        '\n[verifier]\ntimeout_sec = 1800\nenvironment_mode = "separate"\n'
        f'\n[verifier.env]\nFC_EVAL_CASE = {q(target["id"])}\nFC_EVAL_SUITE_SHA256 = {q(target["suite_sha256"])}\n'
        f'FC_EVAL_CORE_SHA256 = {q(target["core_sha256"])}\n'
        f'\n[verifier.environment]\nos = "linux"\ncpus = 4\nmemory_mb = 8192\nbuild_timeout_sec = 1800\n'
        f'docker_image = {q(execution["verifier_image"])}\nnetwork_mode = "no-network"\n')
    (task/'environment/Dockerfile').write_text(
        f'FROM {execution["solver_image"]}\nCOPY --chown=1000:1000 workspace /app\nWORKDIR /app\n'
        'RUN mkdir -p /app/.lake && ln -s /opt/fc-suite/packages /app/.lake/packages\nUSER 1000:1000\n')
    tests=task/'tests';tests.mkdir()
    # The verifier image owns /tests/test.sh; this copy documents the command it runs.
    (tests/'test.sh').write_text(TEST_SCRIPT)


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
