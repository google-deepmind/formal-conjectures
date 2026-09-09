"""Pinned workspace generation and qualified GitHub verification dispatch."""
import json
import re
import shutil
import subprocess
import time
from pathlib import Path
from . import report as rr
from .core import Failure, command, finish, gh, git, github, now, save, start_run

PINS = {
 'generator': ('williamjblair/lean-eval-generator','e611b55d7097b9de973cbe0cef0f0cfad66dbe92'),
 'comparator': ('williamjblair/comparator','deec4b96fc443f9d5c4dbf3dcfb148a95be76f21'),
 'landrun': ('Zouuup/landrun','811cfff51ceaf3d9843708aa6d22e9b84ccac8b4'),
 'nanoda': ('ammkrn/nanoda_lib','05055695879dfebb6628a67da88ceca6cd6b0421'),
}

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
    problem=select(load(root,args.catalog),args.target)
    repository=public_repository(args.repository or git(root,'remote','get-url','origin').decode().strip())
    revision=git(root,'rev-parse',args.source_ref).decode().strip()
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
        exporter.ROOT=root
        out=args.out.resolve()
        result=exporter.export(root/path,problem['theorem'],out,generator,revision,
                                f'https://github.com/{repository}.git')
        provenance=rr.read_json(result/'fc-provenance.json')
        save(directory/'trusted-target.json',provenance)
        save(root/'.conjectures/targets'/f"{rr.digest(str(result).encode())}.json",
             {'workspace':str(result),'init_run':record['id'],'provenance':provenance})
        return finish(directory,record,'pass',workspace=str(result),next_action='Develop Submission.lean, commit the workspace publicly, then run conjectures verify DIR.')
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
    directory,record=start_run(root,'verify',target=trusted['source'],candidate={'repository':repository,'commit':revision,'path':relative},
                               executor={'repository':executor_repo,'commit':ref},producer_kind='hosted_verification')
    inputs={'run_id':record['id'],'candidate_repository':repository,'candidate_commit':revision,
      'candidate_path':relative,'source_repository':trusted['source']['repository'],
      'source_commit':trusted['source']['commit'],'source_path':trusted['source']['path'],
      'declaration':trusted['source']['declaration']}
    save(directory/'request.json',inputs)
    args=['workflow','run','comparator-lean-4-33.yml','--repo',executor_repo,'--ref',ref]
    for k,v in inputs.items():args += ['-f',f'{k}={v}']
    try:
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
    if operation=='cancel':
        gh('run','cancel',identity,'--repo',repo)
        record.update(status='cancellation_requested');save(directory/'run.json',record);return record
    result=rr.parse(gh('run','view',identity,'--repo',repo,'--json','status,conclusion,url'))
    if result['status']!='completed':
        record.update(status=result['status'],outcome='incomplete',url=result['url'])
        save(directory/'run.json',record);return record
    destination=directory/'remote'
    if not destination.exists():
        gh('run','download',identity,'--repo',repo,'--name','verification-'+record['id'],'--dir',str(destination))
    result_path=destination/'verification.json'
    if not result_path.is_file():
        return finish(directory,record,'error',reason='missing_result',workflow_conclusion=result['conclusion'])
    value=rr.read_json(result_path)
    if value.get('request')!=rr.read_json(directory/'request.json'):
        raise Failure('result_binding_mismatch','Remote result does not match this exact request',3)
    if value.get('toolkit_commit')!=record['executor']['commit']:
        raise Failure('executor_binding_mismatch','Result was produced by another toolkit revision',3)
    outcome=value.get('outcome')
    if outcome not in ('pass','fail','error'):raise Failure('invalid_result','Unknown verification outcome',3)
    if result['conclusion']!='success' and outcome=='pass':raise Failure('incomplete_executor','Failed workflow cannot establish success',3)
    return finish(directory,record,outcome,result=value,url=result['url'],producer='github_actions')
