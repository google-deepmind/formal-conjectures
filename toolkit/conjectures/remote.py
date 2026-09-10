"""Trusted Linux verification controller. Candidate files never choose commands or receipts."""
import json
import os
import re
import shutil
import socket
import subprocess
import sys
from pathlib import Path
from . import exporter, report as rr
from .core import Failure, command, git, now, save
from .proof import PINS
from .verifier_result import typed_result

FIELDS = {'run_id','candidate_repository','candidate_commit','candidate_path','source_repository',
          'source_commit','source_path','declaration'}

def validate_request(request):
    rr.obj(request,' '.join(sorted(FIELDS)),'verification request')
    rr.require(re.fullmatch(r'[0-9]{8}T[0-9]{6}Z-[a-f0-9]{12}',request['run_id']) is not None,'Invalid run ID')
    for field in ('candidate_commit','source_commit'):
        rr.require(re.fullmatch('[a-f0-9]{40}',request[field]) is not None,'Expected exact commit')
    rr.require(re.fullmatch(r'[\w.-]+/[\w.-]+',request['candidate_repository']) is not None,'Invalid candidate repository')
    rr.require(re.fullmatch(r'https://github.com/[\w.-]+/[\w.-]+(?:\.git)?',request['source_repository']) is not None,'Invalid source repository')
    rr.relative(request['source_path'])
    if request['candidate_path']!='.':rr.relative(request['candidate_path'])
    rr.text(request['declaration'],'declaration')

def qualify():
    if sys.platform!='linux':raise Failure('unqualified_executor','Verification requires qualified Linux',3)
    try:
        sock=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM);sock.close()
    except OSError:pass
    else:raise Failure('unqualified_executor','AF_UNIX restriction is missing',3)
    for name in ('COMPARATOR_BIN','COMPARATOR_LANDRUN','COMPARATOR_LEAN4EXPORT','COMPARATOR_NANODA'):
        if not Path(os.environ.get(name,'/missing')).is_file():raise Failure('missing_tool',name,3)

def load_submission(checkout,revision,subdir):
    prefix='' if subdir=='.' else subdir+'/'
    try:files=rr.snapshot_files(git(checkout,'archive','--format=tar',revision))
    except ValueError as error:raise Failure('disallowed_submission',str(error),1) from error
    result={name[len(prefix):]:raw for name,raw in files.items() if name.startswith(prefix) and
        (name[len(prefix):]=='Submission.lean' or name[len(prefix):].startswith('Submission/'))}
    if 'Submission.lean' not in result:raise Failure('missing_submission','Submission.lean is required',1)
    if any(not name.endswith('.lean') for name in result):raise Failure('disallowed_submission','Only Lean submission files are permitted',1)
    return result

def invoke_comparator(arguments, workspace, output):
    """Only a typed result can establish rejection; failed invocation text cannot."""
    result_path=output/'comparator-result.json'
    with (output/'verifier.log').open('wb') as log:
        proc=subprocess.run(arguments,cwd=workspace,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    if not result_path.is_file():raise Failure('missing_verifier_result','Comparator produced no typed result; policy not evaluated',3)
    return typed_result(result_path.read_bytes(),proc.returncode),proc.returncode


def execute(request,output,toolkit,source,candidate,generator,producer='github_actions'):
    validate_request(request)
    output.mkdir(parents=True,exist_ok=True)
    record={'schema_version':'fc.proof-verification.v1','request':request,'producer':producer,
            'started_at':now(),'outcome':'error','policy_outcome':'not_evaluated','pins':PINS,
            'toolkit_commit':git(toolkit,'rev-parse','HEAD').decode().strip()}
    workspace=None;prepared=False
    try:
        qualify()
        if git(source,'rev-parse','HEAD').decode().strip()!=request['source_commit']:
            raise Failure('source_binding_mismatch','Source checkout does not match request',3)
        if git(candidate,'rev-parse','HEAD').decode().strip()!=request['candidate_commit']:
            raise Failure('candidate_binding_mismatch','Candidate checkout does not match request',3)
        submissions=load_submission(candidate,request['candidate_commit'],request['candidate_path'])
        # Use the controller's native exporter and template. Candidate repositories supply neither.
        exporter.install_native(source)
        prepared=True
        # A fresh source checkout has no Mathlib artifacts. Populate only its pinned
        # dependencies before the native export, as standalone initialization does.
        with (output/'source-dependencies.log').open('wb') as log:
            subprocess.run(['lake','exe','cache','get'],cwd=source,stdout=log,
                           stderr=subprocess.STDOUT,check=True,timeout=1200)
        exporter.ROOT=source
        workspace=exporter.export(source/request['source_path'],request['declaration'],output/'generated',
                                  generator,request['source_commit'],request['source_repository'])
        config=rr.read_json(workspace/'config.json')
        record['semantic_assessment_required']=bool(config.get('definition_names'))
        if config.get('enable_nanoda') is not True:raise Failure('kernel_policy','Both kernels are required',3)
        # Resolve only trusted generated dependencies before importing any candidate source.
        command(['lake','update'],cwd=workspace,timeout=600)
        command(['lake','exe','cache','get'],cwd=workspace,timeout=1200)
        for name,raw in submissions.items():
            path=workspace/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        result_path=output/'comparator-result.json'
        args=['lake','env',os.environ['COMPARATOR_BIN'],'config.json','--result-json',str(result_path)]
        record.update(submission_files=rr.descriptors(submissions),trusted_config_sha256=rr.digest((workspace/'config.json').read_bytes()),
                      tool_hashes={k:rr.digest(Path(os.environ[k]).read_bytes()) for k in
                      ('COMPARATOR_BIN','COMPARATOR_LANDRUN','COMPARATOR_LEAN4EXPORT','COMPARATOR_NANODA')})
        value,code=invoke_comparator(args,workspace,output)
        record.update(outcome={'pass':'pass','rejected':'fail','error':'error'}[value['outcome']],
                      comparator=value,exit_code=code,
                      policy_outcome=value['outcome'] if value['outcome']!='error' else 'not_evaluated')
    except (Failure,ValueError,OSError,subprocess.SubprocessError,RuntimeError) as error:
        record.update(outcome='fail' if isinstance(error,Failure) and error.code==1 else 'error',
                      reason=getattr(error,'reason','execution_error'),detail=str(error))
    finally:
        # Retain generated sources, policy and logs, not gigabytes of rebuildable
        # dependency artifacts for every attempt. These are controller checkouts.
        for checkout in (source if prepared else None,workspace):
            if checkout is not None:
                cache=checkout/'.lake'
                try:
                    if cache.is_symlink():cache.unlink()
                    elif cache.exists():shutil.rmtree(cache)
                except OSError as error:
                    record.setdefault('cleanup_warnings',[]).append(str(error))
        record['finished_at']=now();save(output/'verification.json',record)
    return record

def main():
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--request',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--producer',choices=['github_actions','local_operator'],default='github_actions')
    for name in ('toolkit','source','candidate','generator'):p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args();result=execute(rr.read_json(args.request),args.out.resolve(),args.toolkit.resolve(),
        args.source.resolve(),args.candidate.resolve(),args.generator.resolve(),args.producer)
    return 0 if result['outcome'] in ('pass','fail') else 3
if __name__=='__main__':raise SystemExit(main())
