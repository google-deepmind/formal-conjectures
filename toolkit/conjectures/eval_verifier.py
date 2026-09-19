"""Harbor's trusted, separate verifier entry point; never run in the agent container.

The verifier image carries every prepared suite workspace and the shared pinned packages.
Verification copies one workspace into container-local storage, imports only submitted Lean
files and runs Comparator without network access or dependency acquisition.
"""
import argparse
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from . import report as rr, remote
from .core import Failure, now, save
from .eval_suite import ROOT, CASE, core_digest, validate_core
from .linux_executor import profile, submission_files
from .unix_restriction import restrict


def run(case,submission,output,suite_sha256=None,core_sha256=None,suite=ROOT,
        toolkit=Path('/opt/fc'),tools=Path('/opt/fc-tools')):
    output.mkdir(parents=True,exist_ok=True)
    if any((output/name).exists() for name in ('fc-result.json','reward.txt','reward.json')):
        raise Failure('output_exists','Verifier output already exists; retain it and use a fresh trial.',3)
    digest=suite_sha256 if isinstance(suite_sha256,str) and re.fullmatch('[a-f0-9]{64}',suite_sha256) else None
    result={'schema_version':'fc.proof-eval-result.v1','task':case if isinstance(case,str) else 'unknown',
            'suite_sha256':digest,'status':'error','policy_outcome':'not_evaluated','started_at':now()}
    try:
        rr.require(digest is not None,'The task must name its frozen suite digest')
        rr.require(isinstance(case,str) and re.fullmatch('[a-z0-9][a-z0-9-]{0,63}',case) is not None,'Invalid case ID')
        core=rr.read_json(suite/'suite-core.json');validate_core(core)
        target=rr.read_json(suite/'cases'/case/'target.json')
        rr.require(target.get('schema_version')==CASE and target.get('id')==case,'Invalid prepared case')
        # The task names the suite core it was exported from; the image must carry exactly that core.
        if core_digest(core)!=target['core_sha256'] or core_sha256!=target['core_sha256']:
            raise Failure('suite_binding_mismatch','Verifier image was prepared for another suite.',3)
        result['core_sha256']=target['core_sha256']
        restrict()
        executor=profile(toolkit,tools,check_systemd=False)
        if executor['ref']!=target['toolkit_commit']:
            raise Failure('executor_binding_mismatch','Verifier image contains another toolkit revision.',3)
        for name,info in executor['binaries'].items():os.environ[name]=info['path']
        submissions=submission_files(submission)
        prepared=suite/'cases'/case/'workspace'
        if rr.read_json(prepared/'fc-provenance.json')['source']!=target['source']:
            raise Failure('changed_target','Prepared workspace provenance differs from its case record.',3)
        record={'schema_version':'fc.proof-verification.v1','producer':'harbor_verifier','target':target['source'],
                'core_sha256':target['core_sha256'],'toolkit_commit':executor['ref'],'started_at':now(),
                'outcome':'error','policy_outcome':'not_evaluated'}
        with tempfile.TemporaryDirectory(prefix='fc-grade-') as d:
            workspace=Path(d)/'workspace'
            # Build outputs stay in container-local storage; shared packages remain read-only.
            shutil.copytree(prepared,workspace,ignore=shutil.ignore_patterns('.lake'))
            (workspace/'.lake').mkdir()
            (workspace/'.lake/packages').symlink_to(suite/'packages')
            try:
                remote.check_workspace(workspace,submissions,output/'verification',record)
            finally:
                record['finished_at']=now();save(output/'verification'/'verification.json',record)
        status={'pass':'verified','fail':'rejected','error':'error'}[record['outcome']]
        if status=='verified' and record.get('semantic_assessment_required'):
            status='assessment_required'
        result.update(status=status,policy_outcome=record['policy_outcome'],verification=record)
    except (Failure,ValueError,KeyError,TypeError,OSError,subprocess.SubprocessError) as error:
        result.update(status='rejected' if isinstance(error,Failure) and error.code==1 else 'error',
                      reason=getattr(error,'reason','execution_error'),detail=str(error))
    result['finished_at']=now();save(output/'fc-result.json',result)
    # Missing reward makes infrastructure/manual-assessment cases non-scored in Harbor.
    # They are never silently turned into an unsuccessful mathematical attempt.
    if result['status'] in ('verified','rejected'):
        (output/'reward.txt').write_text('1\n' if result['status']=='verified' else '0\n')
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case',default=os.environ.get('FC_EVAL_CASE'))
    p.add_argument('--suite-sha256',default=os.environ.get('FC_EVAL_SUITE_SHA256'))
    p.add_argument('--core-sha256',default=os.environ.get('FC_EVAL_CORE_SHA256'))
    for name in ('submission','out'):p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args()
    try:value=run(args.case,args.submission,args.out,args.suite_sha256,args.core_sha256)
    except Failure as error:
        print(str(error));return error.code
    return {'verified':0,'rejected':0,'assessment_required':4,'error':3}[value['status']]


if __name__=='__main__':raise SystemExit(main())
