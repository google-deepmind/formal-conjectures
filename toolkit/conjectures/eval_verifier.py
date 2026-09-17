"""Harbor's trusted, separate verifier entry point; never run in the agent container."""
import argparse
import os
import subprocess
import tempfile
from pathlib import Path
from . import report as rr, remote
from .core import Failure, git, now, save, start_run
from .linux_executor import profile, submission_files
from .unix_restriction import restrict


def run(target_path,submission,output,toolkit=Path('/opt/fc'),tools=Path('/opt/fc-tools')):
    output.mkdir(parents=True,exist_ok=True)
    if any((output/name).exists() for name in ('fc-result.json','reward.txt','reward.json')):
        raise Failure('output_exists','Verifier output already exists; retain it and use a fresh trial.',3)
    result={'schema_version':'fc.proof-eval-result.v1','task':'unknown','suite_sha256':None,
            'status':'error','policy_outcome':'not_evaluated','started_at':now()}
    try:
        target=rr.read_json(target_path)
        rr.require(target.get('schema_version')=='fc.proof-task.v1','Invalid proof task')
        result.update(task=target['id'],suite_sha256=target['suite_sha256'])
        restrict()
        executor=profile(toolkit,tools,check_systemd=False)
        if executor['ref']!=target['toolkit_commit']:
            raise Failure('executor_binding_mismatch','Verifier image contains another toolkit revision.',3)
        for name,info in executor['binaries'].items():os.environ[name]=info['path']
        with tempfile.TemporaryDirectory(prefix='fc-grade-') as d:
            root=Path(d);candidate=root/'candidate';candidate.mkdir()
            for name,raw in submission_files(submission).items():
                p=candidate/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
            git(candidate,'init');git(candidate,'add','.')
            git(candidate,'-c','user.name=FC evaluator','-c','user.email=eval@localhost','-c','commit.gpgsign=false','commit','-qm','Frozen evaluation submission')
            _,attempt=start_run(root,'verify')
            source=target['source']
            request={'run_id':attempt['id'],'candidate_repository':'local/submission',
                     'candidate_commit':git(candidate,'rev-parse','HEAD').decode().strip(),'candidate_path':'.',
                     'source_repository':source['repository'],'source_commit':source['commit'],
                     'source_path':source['path'],'declaration':source['declaration']}
            remote.validate_request(request)
            checkout=root/'source';git(root,'init',checkout)
            git(checkout,'fetch','--depth','1',source['repository'],source['commit'])
            git(checkout,'checkout','--detach',source['commit'])
            verification=remote.execute(request,output/'verification',toolkit,checkout,candidate,tools/'generator',producer='local_operator')
            status={'pass':'verified','fail':'rejected','error':'error'}[verification['outcome']]
            if status=='verified' and verification.get('semantic_assessment_required'):
                status='assessment_required'
            result.update(status=status,policy_outcome=verification['policy_outcome'],verification=verification)
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
    for name in ('target','submission','out'):p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args()
    try:value=run(args.target,args.submission,args.out)
    except Failure as error:
        print(str(error));return error.code
    return {'verified':0,'rejected':0,'assessment_required':4,'error':3}[value['status']]


if __name__=='__main__':raise SystemExit(main())
