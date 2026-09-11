"""Local Linux transport for the same trusted controller used by Actions.

Configuration is operator supplied. Candidate files never select tools or policy.
"""
import json
import os
import re
import stat
import subprocess
import sys
from pathlib import Path
from . import report as rr
from .core import Failure, command, finish, git, save, start_run
from .proof import PINS
from .ui import stage, log_location


def profile(toolkit, tools, check_systemd=True):
    if sys.platform != 'linux' or os.getuid() == 0:
        raise Failure('unqualified_executor','Use an unprivileged Linux account with systemd and Landrun.',4)
    toolkit=toolkit.resolve();tools=tools.resolve()
    revision=git(toolkit,'rev-parse','HEAD').decode().strip()
    if git(toolkit,'status','--porcelain','--untracked-files=no').strip():
        raise Failure('dirty_executor','Commit the trusted toolkit before configuring execution.',4)
    for name,(repo,pin) in PINS.items():
        checkout=tools/name
        if git(checkout,'rev-parse','HEAD').decode().strip()!=pin or git(checkout,'status','--porcelain','--untracked-files=no').strip():
            raise Failure('tool_pin_mismatch',f'{name} must be built from {repo}@{pin}.',4)
    binaries={
        'COMPARATOR_BIN':tools/'comparator/.lake/build/bin/comparator',
        'COMPARATOR_LANDRUN':tools/'landrun/landrun',
        'COMPARATOR_NANODA':tools/'nanoda/target/release/nanoda_bin',
        'COMPARATOR_LEAN4EXPORT':toolkit/'comparator/verifier/.lake/packages/lean4export/.lake/build/bin/lean4export',
    }
    for name,path in binaries.items():
        if not path.is_file():raise Failure('missing_tool',f'Build the pinned tool before setup: {path}',4)
    probe='import socket\ntry:\n socket.socket(socket.AF_UNIX)\nexcept OSError:\n pass\nelse:\n raise SystemExit("AF_UNIX restriction missing")\n'
    if check_systemd:
        command(['systemd-run','--user','--wait','--pipe','--collect','--property=RestrictAddressFamilies=~AF_UNIX',
                 sys.executable,'-c',probe],timeout=30)
    return {'kind':'linux','toolkit':str(toolkit),'ref':revision,'tools':str(tools),
            'binaries':{name:{'path':str(path),'sha256':rr.digest(path.read_bytes())} for name,path in binaries.items()},
            'qualification':'operator_configured; exact pins and sandbox prerequisites checked; release qualification remains separate'}


def validate(value):
    current=profile(Path(value['toolkit']),Path(value['tools']))
    if current != value:raise Failure('executor_changed','Executor revision or binary digest changed; rerun setup verify --local.',4)


def submission_files(candidate):
    # Descriptor-relative opens prevent a concurrent symlink swap from importing
    # files outside the selected submission. Reads and traversal are bounded.
    files={};entries=0;total=0
    def collect(parent,name,relative,depth=0):
        nonlocal entries,total
        entries+=1
        if entries>1000 or depth>32:
            raise Failure('submission_too_large','Submission directory exceeds traversal limits.',1)
        try:fd=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=parent)
        except OSError as error:
            raise Failure('disallowed_submission','Submission files must be readable and cannot be symlinks.',1) from error
        try:
            mode=os.fstat(fd).st_mode
            if stat.S_ISDIR(mode) and relative!='Submission.lean':
                with os.scandir(fd) as children:
                    for child in children:collect(fd,child.name,relative+'/'+child.name,depth+1)
                return
            if not stat.S_ISREG(mode) or not relative.endswith('.lean'):
                raise Failure('disallowed_submission','Only regular Lean submission files are allowed.',1)
            with os.fdopen(os.dup(fd),'rb') as stream:raw=stream.read(8*1024*1024+1)
            if len(raw)>8*1024*1024:
                raise Failure('submission_too_large','Submission file exceeds 8 MiB.',1)
            total+=len(raw);files[relative]=raw
            if len(files)>200 or total>32*1024*1024:
                raise Failure('submission_too_large','Submission exceeds 200 files or 32 MiB.',1)
        finally:os.close(fd)
    descriptor=os.open(candidate,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:
        collect(descriptor,'Submission.lean','Submission.lean')
        try:os.stat('Submission',dir_fd=descriptor,follow_symlinks=False)
        except FileNotFoundError:pass
        else:collect(descriptor,'Submission','Submission')
    finally:os.close(descriptor)
    return files


def verify_local(root,candidate,trusted,executor):
    directory,record=start_run(root,'verify',target=trusted['source'],producer_kind='local_operator',executor=executor)
    try:
        validate(executor)
        files=submission_files(candidate)
        snapshot=directory/'candidate';snapshot.mkdir()
        for name,raw in files.items():
            path=snapshot/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
        git(snapshot,'init');git(snapshot,'add','Submission.lean',*(['Submission'] if (snapshot/'Submission').exists() else []))
        git(snapshot,'-c','user.name=FC verification','-c','user.email=local@localhost','-c','commit.gpgsign=false','commit','-qm','Frozen local submission')
        target=trusted['source']
        request={'run_id':record['id'],'candidate_repository':'local/submission',
                 'candidate_commit':git(snapshot,'rev-parse','HEAD').decode().strip(),'candidate_path':'.',
                 'source_repository':target['repository'],'source_commit':target['commit'],
                 'source_path':target['path'],'declaration':target['declaration']}
        from .remote import validate_request
        validate_request(request)
        save(directory/'request.json',request)
        source=directory/'source';git(directory,'init',source)
        git(source,'fetch','--depth','1',request['source_repository'],request['source_commit'])
        git(source,'checkout','--detach',request['source_commit'])
        output=directory/'remote'
        unit='fc-verify-'+record['id']
        args=['systemd-run','--user','--wait','--pipe','--collect','--unit='+unit,
              '--property=RuntimeMaxSec=3600','--property=RestrictAddressFamilies=~AF_UNIX',
              '--setenv=PATH='+os.environ['PATH'],'--setenv=PYTHONPATH='+str(Path(executor['toolkit'])/'toolkit')]
        args += ['--setenv='+name+'='+value['path'] for name,value in executor['binaries'].items()]
        args += [sys.executable,'-m','conjectures.remote','--producer','local_operator','--request',str(directory/'request.json'),
                 '--out',str(output),'--toolkit',executor['toolkit'],'--source',str(source),
                 '--candidate',str(snapshot),'--generator',str(Path(executor['tools'])/'generator')]
        stage('Verifying frozen local submission on Linux');log_location(directory/'executor.log')
        try:
            with (directory/'executor.log').open('wb') as log:
                process=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,timeout=3660)
        except (KeyboardInterrupt,subprocess.TimeoutExpired):
            command(['systemctl','--user','stop',unit],timeout=30)
            raise
        path=output/'verification.json'
        if not path.is_file():raise Failure('missing_result','Linux executor produced no result; inspect executor.log.',3)
        result=rr.read_json(path)
        if result.get('request')!=request or result.get('toolkit_commit')!=executor['ref'] or result.get('producer')!='local_operator':
            raise Failure('result_binding_mismatch','Executor result does not match this request.',3)
        if process.returncode!=0 and result.get('outcome')=='pass':raise Failure('incomplete_executor','Executor failed before successful completion.',3)
        if result.get('outcome') not in ('pass','fail','error'):raise Failure('invalid_result','Unknown verifier outcome.',3)
        return finish(directory,record,result['outcome'],result=result,candidate={'files':rr.descriptors(files)},
                      next_action='Inspect with conjectures run show '+record['id'])
    except KeyboardInterrupt:
        finish(directory,record,'cancelled',reason='interrupted');raise
    except (Failure,ValueError,OSError,subprocess.SubprocessError) as error:
        return finish(directory,record,'fail' if isinstance(error,Failure) and error.code==1 else 'error',
                      reason=getattr(error,'reason','execution_error'),detail=str(error),policy_outcome='not_evaluated')
