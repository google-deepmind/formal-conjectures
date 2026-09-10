"""One trusted Actions publisher. Local clients only dispatch and read receipts."""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path
from . import report as rr
from .core import Failure, gh, github, now, save, run_lock

WORKFLOW='contribution-publisher.yml'
MARKER='<!-- fc-designated-advisory-v1 -->'
FIELDS='request_id run_id pr archive_repository archive_commit manifest_sha256'


def tag_for(repository, revision):
    # Shared GitHub dispatch semantics; importing the proof executor is unnecessary.
    from .core import command
    raw=command(['git','ls-remote','--tags',f'https://github.com/{repository}.git']).decode()
    refs=dict(line.split()[::-1] for line in raw.splitlines())
    tags=[ref.removeprefix('refs/tags/') for ref,sha in refs.items()
          if not ref.endswith('^{}') and refs.get(ref+'^{}',sha)==revision]
    if not tags:raise Failure('publisher_tag_required','Push a tag for the qualified publisher revision before setup.',4)
    return sorted(tags)[0]


def validate_setup(repository, revision):
    from .onboarding import contents, public_repo, RESOURCES
    public_repo(repository)
    if not re.fullmatch('[0-9a-f]{40}',revision):raise Failure('unpinned_publisher','Use a full publisher commit SHA.',4)
    expected=(RESOURCES/'publisher-workflow.yml').read_bytes()
    if contents(repository,'.github/workflows/'+WORKFLOW,revision)!=expected:
        raise Failure('publisher_policy_mismatch','Publisher workflow differs from the bundled policy.',4)
    tag_for(repository,revision)
    return {'repository':repository,'ref':revision}


def dispatch(directory, publication, cfg):
    publisher=(cfg.get('evidence') or {}).get('publisher')
    if not publisher:raise Failure('publisher_not_configured','Archive retained. Configure setup evidence --publisher-repository OWNER/REPO --publisher-ref COMMIT before --post.',4)
    ticket=rr.read_json(directory/'ticket.json');record=rr.read_json(directory/'run.json')
    if publisher['repository']!=ticket['repository']:
        raise Failure('publisher_repository_mismatch','The publisher must run in the repository that owns this PR.',4)
    previous=directory/'publisher.json'
    if previous.is_file():
        value=rr.read_json(previous)
        if value['status'] not in ('error','cancelled'):
            return {**value,'command_status':'success' if value['status'] in ('queued','in_progress','posted') else 'incomplete'}
        save(directory/'publisher-history'/(value['request']['request_id']+'.json'),value)
    validate_setup(publisher['repository'],publisher['ref'])
    request={'request_id':uuid.uuid4().hex,'run_id':record['id'],'pr':str(ticket['pr']),
             'archive_repository':publication['repository'],'archive_commit':publication['commit'],
             'manifest_sha256':publication['manifest_sha256']}
    value={'schema_version':'fc.publisher-operation.v1','request':request,'publisher':publisher,
           'status':'dispatching','created_at':now(),'next_action':'conjectures run wait '+record['id']}
    save(previous,value)
    args=['workflow','run',WORKFLOW,'--repo',publisher['repository'],'--ref',tag_for(publisher['repository'],publisher['ref'])]
    for key,item in request.items():args+=['-f',key+'='+item]
    # An uncertain dispatch is not automatically retried: it may already exist remotely.
    gh(*args)
    value.update(status='queued');save(previous,value)
    return {**value,'command_status':'success'}


def control(directory, operation):
    value=rr.read_json(directory/'publisher.json');repo=value['publisher']['repository']
    if value['status'] in ('posted','historical','superseded','cancelled','error'):
        return {**value,'command_status':{'posted':'success','cancelled':'cancelled','error':'error'}.get(value['status'],'incomplete')}
    if not value.get('remote_run_id'):
        candidates=rr.parse(gh('run','list','--repo',repo,'--workflow',WORKFLOW,'--limit','100','--json','databaseId,displayTitle,headSha'))
        found=[r for r in candidates if r['displayTitle']=='FC publication '+value['request']['request_id'] and r['headSha']==value['publisher']['ref']]
        if len(found)!=1:raise Failure('run_not_visible','Publisher is not uniquely visible yet. Retry run wait; do not redispatch.',4)
        value['remote_run_id']=found[0]['databaseId'];save(directory/'publisher.json',value)
    identity=str(value['remote_run_id'])
    remote=rr.parse(gh('run','view',identity,'--repo',repo,'--json','status,conclusion,url'))
    value['url']=remote['url']
    if operation=='cancel' and remote['status']!='completed':
        gh('run','cancel',identity,'--repo',repo);value.update(status='cancellation_requested',cancellation_requested_at=now())
    elif remote['status']!='completed':
        value.update(status='cancellation_requested' if value.get('cancellation_requested_at') else remote['status'],remote_status=remote['status'])
    else:
        output=directory/'publisher-artifacts'/value['request']['request_id'];output.mkdir(parents=True,exist_ok=True)
        try:
            (output/'publisher.log').write_bytes(gh('run','view',identity,'--repo',repo,'--log'))
        except Failure as error:(output/'publisher.log').write_text('Workflow log unavailable: '+str(error))
        try:
            gh('run','download',identity,'--repo',repo,'--name','publication-'+value['request']['request_id'],'--dir',str(output))
            receipt=rr.read_json(output/'receipt.json')
            rr.require(receipt['request']==value['request'] and receipt['publisher_commit']==value['publisher']['ref'] and str(receipt['workflow_run'])==identity,'Publisher receipt binding mismatch')
            rr.require(receipt['status'] in ('posted','historical','superseded','error'),'Invalid publisher outcome')
            if remote['conclusion']!='success' and receipt['status']=='posted':raise ValueError('Incomplete workflow cannot establish publication success')
            value.update(status=receipt['status'],receipt=receipt)
        except (Failure,OSError,ValueError,KeyError) as error:
            value.update(status='cancelled' if remote['conclusion']=='cancelled' else 'error',
                         reason='remote_cancelled' if remote['conclusion']=='cancelled' else 'publisher_result_unavailable',detail=str(error))
    save(directory/'publisher.json',value)
    status=value['status']
    return {**value,'command_status':'success' if status in ('posted','cancellation_requested') else 'cancelled' if status=='cancelled' else 'error' if status=='error' else 'incomplete'}


def wait(directory, timeout):
    deadline=time.monotonic()+timeout;previous=None
    while True:
        try:
            with run_lock(directory):value=control(directory,'wait')
        except Failure as error:
            if error.reason not in ('run_not_visible','run_busy'):raise
            value={'status':error.reason,'command_status':'incomplete'}
        state=value['status']
        if state in ('posted','historical','superseded','cancelled','error'):return value
        if state!=previous:print('Publication: '+state+'…',file=sys.stderr);previous=state
        if time.monotonic()>=deadline:return {**value,'reason':'wait_timeout','command_status':'incomplete'}
        time.sleep(min(5,max(0,deadline-time.monotonic())))


def write_comment(endpoint, body, method):
    with tempfile.NamedTemporaryFile(mode='w',suffix='.json') as file:
        json.dump({'body':body},file);file.flush()
        return rr.parse(gh('api',endpoint,'--method',method,'--input',file.name))


def publish_comment(request, repository, archive_repository, archive_branch):
    """Invoked only by the serialized, trusted workflow, never by CLI dispatch."""
    from .evidence_reader import load
    rr.obj(request,FIELDS,'publisher request')
    rr.require(bool(re.fullmatch('[0-9a-f]{32}',request['request_id'])),'Invalid request ID')
    rr.require(bool(re.fullmatch('[1-9][0-9]*',request['pr'])),'Invalid PR number')
    rr.require(bool(re.fullmatch('[0-9a-f]{40}',request['archive_commit'])),'Invalid archive revision')
    rr.require(request['archive_repository']==archive_repository and bool(archive_branch),'Archive is not the configured destination')
    current=load(destination={'repository':archive_repository,'branch':archive_branch})
    pinned=load(destination={'repository':archive_repository,'branch':request['archive_commit']})
    def select(index):
        rr.require(index['status']=='available','Evidence is unavailable or invalid')
        matches=[r for r in index['runs'] if r['id']==request['run_id'] and r['manifest_sha256']==request['manifest_sha256']]
        rr.require(len(matches)==1,'Run is not registered with these immutable bytes')
        return matches[0]
    select(current);run=select(pinned);target=run['target']
    rr.require(run['kind']=='review' and target['repository']==repository and str(target['pr'])==request['pr'],'Publication target mismatch')
    def observe():
        pr=github(f"repos/{repository}/pulls/{request['pr']}")
        return {'state':pr['state'],'head':pr['head']['sha'],'base':pr['base']['sha'],'observed_at':now()}
    def fresh(value):return value['state']=='open' and all(value[key]==target[key] for key in ('head','base'))
    before=observe()
    if not fresh(before):return {'status':'historical','before':before,'reason':'target_changed'}
    comments=[]
    for page in range(1,101):
        batch=github(f"repos/{repository}/issues/{request['pr']}/comments?per_page=100&page={page}");comments+=batch
        if len(batch)<100:break
    else:raise ValueError('Comment pagination limit exceeded')
    existing=[c for c in comments if c['user']['login']=='github-actions[bot]' and c['user'].get('type')=='Bot' and c['body'].startswith(MARKER)]
    rr.require(len(existing)<=1,'Multiple designated comments require reconciliation')
    order=(run['created_at'],run['id'])
    if existing:
        match=re.search(r'<!-- fc-review-order: (\S+) (\S+) -->',existing[0]['body'])
        rr.require(match is not None,'Existing designated comment has no ordering record')
        if match.groups()>order:return {'status':'superseded','before':before,'reason':'newer_report_posted'}
    summary=run['summary']
    body=f"{MARKER}\n**Advisory FC review — {rr.escape(summary['semantic_verdict'])}**\n\nReviewed `{target['head']}` against `{target['base']}`. Coverage: {summary['completeness']}.\n\nOperator-produced review, published by the designated workflow. Maintainers decide acceptance.\n"
    for finding in summary['findings'][:20]:body+=f"\n- {rr.escape(finding['file'])}:{finding['line']} — {rr.escape(finding['message'][:1500])}"
    body+=f"\n\n[Immutable report and provenance]({run['url']}). Later input changes make this report historical.\n\n<!-- fc-review-order: {order[0]} {order[1]} -->"
    before=observe()
    if not fresh(before):return {'status':'historical','before':before,'reason':'target_changed'}
    comment=existing[0] if existing and existing[0]['body']==body else write_comment(
        f"repos/{repository}/issues/comments/{existing[0]['id']}" if existing else f"repos/{repository}/issues/{request['pr']}/comments",body,'PATCH' if existing else 'POST')
    after=observe()
    return {'status':'posted' if fresh(after) else 'historical','before':before,'after':after,
            'comment_url':comment['html_url'],'comment_id':comment['id']}


def main():
    output=Path(sys.argv[1]);request=json.loads(os.environ['PUBLISH_REQUEST'])
    receipt={'schema_version':'fc.publisher-receipt.v1','request':request,'publisher_commit':os.environ['GITHUB_SHA'],
             'workflow_run':os.environ['GITHUB_RUN_ID'],'started_at':now(),'status':'error'}
    try:receipt.update(publish_comment(request,os.environ['GITHUB_REPOSITORY'],os.environ.get('FC_EVIDENCE_REPOSITORY'),os.environ.get('FC_EVIDENCE_BRANCH')))
    except (Failure,ValueError,OSError,KeyError,TypeError,subprocess.SubprocessError) as error:receipt.update(reason=getattr(error,'reason','publisher_error'),detail=str(error))
    receipt['finished_at']=now();save(output/'receipt.json',receipt)
    return 3 if receipt['status']=='error' else 0


if __name__=='__main__':raise SystemExit(main())
