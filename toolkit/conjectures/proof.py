"""Pinned workspace generation and qualified GitHub verification dispatch."""
import json
import re
import shutil
import subprocess
import time
import sys
import tempfile
import shlex
from pathlib import Path
from . import report as rr
from .core import Failure, command, finish, gh, git, github, now, save, start_run, run_lock

PINS = {
 'generator': ('williamjblair/lean-eval-generator','e611b55d7097b9de973cbe0cef0f0cfad66dbe92'),
 'comparator': ('williamjblair/comparator','deec4b96fc443f9d5c4dbf3dcfb148a95be76f21'),
 'landrun': ('Zouuup/landrun','811cfff51ceaf3d9843708aa6d22e9b84ccac8b4'),
 'nanoda': ('ammkrn/nanoda_lib','05055695879dfebb6628a67da88ceca6cd6b0421'),
}

def executor_ref(repository, revision):
    """GitHub dispatch accepts named refs, not commit SHAs. Require a matching tag."""
    raw=command(['git','ls-remote','--tags',f'https://github.com/{repository}.git']).decode()
    refs=dict(line.split()[::-1] for line in raw.splitlines())
    tags=[]
    for ref,sha in refs.items():
        if ref.endswith('^{}'):continue
        if refs.get(ref+'^{}',sha)==revision:tags.append(ref.removeprefix('refs/tags/'))
    if not tags:
        raise Failure('executor_tag_required',
            'GitHub requires a named ref. Tag the qualified executor commit and push the tag, then retry setup verify. No tag is created automatically.',4)
    return sorted(tags,key=lambda name:(not name.startswith('toolkit-v'),name))[0]

def public_repository(url):
    match = re.fullmatch(r'(?:https://github.com/|git@github.com:)?([\w.-]+/[\w.-]+?)(?:\.git)?',url)
    if not match: raise Failure('unsupported_repository','Use a public GitHub repository')
    name = match[1]
    metadata = github('repos/'+name)
    if metadata.get('private') or metadata.get('visibility') not in (None,'public'):
        raise Failure('private_workspace','Private work requires a separately configured qualified Linux executor',4)
    return name

def checkout_tool(root, tool):
    repository, revision = PINS[tool]
    directory = root/'.conjectures/tools'/f'{tool}-{revision}'
    if not directory.exists():
        command(['git','init',directory])
        git(directory,'fetch','--depth','1',f'https://github.com/{repository}.git',revision)
        git(directory,'checkout','--detach',revision)
    if git(directory,'rev-parse','HEAD').decode().strip()!=revision or git(directory,'status','--porcelain').strip():
        raise Failure('tool_pin_mismatch','Tool checkout differs from pin: '+tool)
    return directory

def initialize(root,args,cfg):
    from .catalog import load,select
    from . import exporter
    catalog=load(root,args.catalog);problem=select(catalog,args.target)
    source=catalog.get('provenance',{}).get('source',{})
    repository_name=args.repository or source.get('repository')
    ref=args.source_ref or source.get('commit')
    if not repository_name or not ref:
        raise Failure('source_revision_required','An unversioned local catalog requires explicit --repository OWNER/REPO and --source-ref COMMIT.',2)
    repository=public_repository(repository_name)
    # A published catalog commit need not already exist in the local clone.
    revision=ref if re.fullmatch(r'[0-9a-f]{40}',ref) else git(root,'rev-parse',ref).decode().strip()
    # Verify remote reachability before creating any workspace, without pushing anything.
    if github(f'repos/{repository}/commits/{revision}').get('sha')!=revision:
        raise Failure('unpublished_source','Source commit is not retrievable from its recorded repository',4)
    path=problem.get('githubPath')
    if not path:
        # Convert Lean-printed module components; this is name decoding, not source parsing.
        parts=[];buf='';quoted=False
        for ch in problem['module']:
            if ch=='«':quoted=True
            elif ch=='»':quoted=False
            elif ch=='.' and not quoted:parts.append(buf);buf=''
            else:buf+=ch
        parts.append(buf);path='/'.join(parts)+'.lean'
    rr.relative(path)
    generator=checkout_tool(root,'generator')
    directory,record=start_run(root,'init',target={'repository':repository,'commit':revision,
        'module':problem['module'],'declaration':problem['theorem'],'path':path})
    try:
        out=args.out.resolve()
        if out.exists():raise Failure('output_exists','Choose a new directory for --out; existing files are preserved.')
        print('Generating the exact source workspace at '+revision+'…',file=sys.stderr)
        # Export from an isolated exact checkout, never require switching or cleaning the operator's branch.
        with tempfile.TemporaryDirectory(prefix='fc-export-source-') as temp:
            source=Path(temp).resolve()/'source'
            command(['git','clone','--no-checkout','--shared',root,source])
            git(source,'fetch','--depth','1',f'https://github.com/{repository}.git',revision)
            git(source,'checkout','--detach',revision)
            exporter.install_native(source)
            print('Acquiring pinned source dependencies and the Mathlib cache…',file=sys.stderr)
            command(['lake','exe','cache','get'],cwd=source,timeout=1200)
            previous=exporter.ROOT
            try:
                exporter.ROOT=source
                result=exporter.export(source/path,problem['theorem'],directory/'export',generator,revision,
                                      f'https://github.com/{repository}.git')
            finally:exporter.ROOT=previous
        shutil.copytree(result,out)
        result=out
        provenance=rr.read_json(result/'fc-provenance.json')
        save(directory/'trusted-target.json',provenance)
        save(root/'.conjectures/targets'/f"{rr.digest(str(result).encode())}.json",
             {'workspace':str(result),'init_run':record['id'],'provenance':provenance})
        next_command=shlex.join(['conjectures','--repo',str(root),'verify',str(result)])
        return finish(directory,record,'pass',workspace=str(result),next_action='Develop Submission.lean, commit and push the workspace publicly, then run '+next_command)
    except BaseException as error:
        finish(directory,record,'error',reason=getattr(error,'reason','export_error'),detail=str(error));raise

def verify(root,candidate,cfg):
    candidate=candidate.resolve()
    trusted_path=root/'.conjectures/targets'/f'{rr.digest(str(candidate).encode())}.json'
    if not trusted_path.is_file():
        raise Failure('untrusted_target','Generate this workspace with conjectures init before verification',4)
    trusted=rr.read_json(trusted_path)['provenance']
    if rr.read_json(candidate/'fc-provenance.json')!=trusted:
        raise Failure('changed_target','Workspace provenance differs from the retained trusted target',1)
    executor=cfg.get('executor')
    if not isinstance(executor,dict) or executor.get('kind')!='github':
        raise Failure('executor_unavailable','Configure a qualified GitHub Linux executor',4)
    repository=public_repository(git(candidate,'remote','get-url','origin').decode().strip())
    repo_root=Path(git(candidate,'rev-parse','--show-toplevel').decode().strip()).resolve()
    relative=candidate.relative_to(repo_root).as_posix()
    if git(candidate,'status','--porcelain','--',str(candidate)).strip():
        raise Failure('uncommitted_workspace','Commit the workspace before remote verification; nothing is uploaded automatically',4)
    revision=git(candidate,'rev-parse','HEAD').decode().strip()
    if github(f'repos/{repository}/commits/{revision}').get('sha')!=revision:
        raise Failure('unpublished_workspace','Push the proof workspace explicitly before remote verification',4)
    executor_repo=public_repository(executor['repository']);ref=executor['ref']
    if not re.fullmatch('[0-9a-f]{40}',ref):raise Failure('unpinned_executor','Executor ref must be an exact qualified commit',4)
    dispatch_ref=executor_ref(executor_repo,ref)
    directory,record=start_run(root,'verify',target=trusted['source'],candidate={'repository':repository,'commit':revision,'path':relative},
                               executor={'repository':executor_repo,'commit':ref,'dispatch_ref':dispatch_ref},producer_kind='hosted_verification')
    inputs={'run_id':record['id'],'candidate_repository':repository,'candidate_commit':revision,
      'candidate_path':relative,'source_repository':trusted['source']['repository'],
      'source_commit':trusted['source']['commit'],'source_path':trusted['source']['path'],
      'declaration':trusted['source']['declaration']}
    save(directory/'request.json',inputs)
    args=['workflow','run','comparator-lean-4-33.yml','--repo',executor_repo,'--ref',dispatch_ref]
    for k,v in inputs.items():args += ['-f',f'{k}={v}']
    try:
        print('Dispatching verification to '+executor_repo+'…',file=sys.stderr)
        gh(*args)
        record.update(status='queued',outcome='incomplete',next_action='Use conjectures run wait '+record['id'])
        save(directory/'run.json',record);return record
    except BaseException as error:
        finish(directory,record,'error',reason='dispatch_error',detail=str(error));raise

def control(directory,record,operation):
    if record['kind']!='verify':
        raise Failure('unsupported_control','Local foreground runs cannot be controlled after they exit',4)
    repo=record['executor']['repository']
    if not record.get('remote_run_id'):
        matches=rr.parse(gh('run','list','--repo',repo,'--workflow','comparator-lean-4-33.yml','--limit','100',
                         '--json','databaseId,displayTitle,headSha,status,conclusion'))
        found=[x for x in matches if x['displayTitle']=='FC verification '+record['id'] and x['headSha']==record['executor']['commit']]
        if len(found)!=1:raise Failure('run_not_visible','Remote run is not visible yet; retry run wait',4)
        record['remote_run_id']=found[0]['databaseId'];save(directory/'run.json',record)
    identity=str(record['remote_run_id'])
    result=rr.parse(gh('run','view',identity,'--repo',repo,'--json','status,conclusion,url'))
    if operation=='cancel' and result['status']!='completed':
        gh('run','cancel',identity,'--repo',repo)
        record.update(status='cancellation_requested',cancellation_requested_at=now())
        save(directory/'run.json',record);return record
    if result['status']!='completed':
        state='cancellation_requested' if record.get('cancellation_requested_at') else result['status']
        record.update(status=state,remote_status=result['status'],outcome='incomplete',url=result['url'])
        save(directory/'run.json',record);return record
    destination=directory/'remote'
    if not destination.exists():
        if result['conclusion']=='cancelled':
            return finish(directory,record,'cancelled',reason='remote_cancelled',url=result['url'])
        artifacts=github(f'repos/{repo}/actions/runs/{identity}/artifacts?per_page=100')
        if not any(a.get('name')=='verification-'+record['id'] and not a.get('expired')
                   for a in artifacts.get('artifacts',[])):
            return finish(directory,record,'error',reason='missing_result',
                          workflow_conclusion=result['conclusion'],url=result['url'])
        with tempfile.TemporaryDirectory(prefix='remote-download-',dir=directory) as temp:
            staging=Path(temp)/'artifacts'
            gh('run','download',identity,'--repo',repo,'--name','verification-'+record['id'],'--dir',str(staging))
            staging.rename(destination)
    result_path=destination/'verification.json'
    if result['conclusion']=='cancelled' and not result_path.is_file():
        return finish(directory,record,'cancelled',reason='remote_cancelled',url=result['url'])
    if not result_path.is_file():
        return finish(directory,record,'error',reason='missing_result',workflow_conclusion=result['conclusion'])
    try:value=rr.read_json(result_path)
    except (ValueError,OSError) as error:return finish(directory,record,'error',reason='invalid_result',detail=str(error))
    if value.get('request')!=rr.read_json(directory/'request.json'):
        return finish(directory,record,'error',reason='result_binding_mismatch',detail='Remote result does not match this exact request')
    if value.get('toolkit_commit')!=record['executor']['commit']:
        return finish(directory,record,'error',reason='executor_binding_mismatch',detail='Result was produced by another toolkit revision')
    outcome=value.get('outcome')
    if outcome not in ('pass','fail','error'):
        return finish(directory,record,'error',reason='invalid_result',detail='Unknown verification outcome')
    if result['conclusion']!='success' and outcome=='pass':
        return finish(directory,record,'error',reason='incomplete_executor',detail='Failed workflow cannot establish success')
    return finish(directory,record,outcome,result=value,url=result['url'],producer='github_actions')


def wait(directory,record,timeout):
    deadline=time.monotonic()+timeout
    previous=None
    while True:
        try:
            with run_lock(directory):
                record=rr.read_json(directory/'run.json')
                if record['status']=='completed':return record
                record=control(directory,record,'wait')
        except Failure as error:
            if error.reason not in ('run_not_visible','run_busy'):raise
            state=error.reason
        else:
            state=record['status']
            if state=='completed':return record
        if state!=previous:
            print('Verification: '+state+'…',file=sys.stderr);previous=state
        remaining=deadline-time.monotonic()
        if remaining<=0:
            return {**record,'command_status':'incomplete','reason':'wait_timeout',
                    'next_action':'Remote work continues. Run conjectures run wait '+record['id']}
        time.sleep(min(5,remaining))
