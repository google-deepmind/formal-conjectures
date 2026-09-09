"""Explicit public exports and immutable evidence-branch publication."""
import json
import re
import tempfile
from pathlib import Path
from urllib.parse import quote
from . import report as rr
from .core import Failure, command, gh, git, github, now, save

MARKER='<!-- fc-advisory-review -->'

def redact(raw,root):
    value=raw.decode('utf-8')
    for path,label in sorted([(str(Path.home()),'<operator-home>'),(str(root),'<workspace>')],key=lambda p:-len(p[0])):
        value=value.replace(path,label)
    return value.encode()

def export(root,directory):
    record=rr.read_json(directory/'run.json')
    if record['status']!='completed':raise Failure('incomplete_run','Only completed runs can be published',4)
    selected={'run.json':rr.encode(record)}
    if record['kind']=='review':
        rebuilt=rr.assemble(directory/'input',directory/'input',directory/'review.json',directory/'evidence')
        if rebuilt['report.json']!=(directory/'bundle/report.json').read_bytes():
            raise Failure('invalid_bundle','Review bundle does not reconstruct from retained evidence',3)
        for name in ('report.json','review.json','request.json'):
            selected[name]=rebuilt[name]
        selected['sources.json']=rr.encode([{'path':s['path'],'sha256':s['sha256'],'availability':'retained_locally'}
                                          for s in rr.parse(rebuilt['request.json'])['sources']])
        references=[]
        for item in rr.parse(rebuilt['request.json'])['sources']:
            if item['path'].endswith('.json'):
                source=rr.parse(rr.read_artifact(directory/'input',item['path']))
                if isinstance(source,dict) and 'url' in source:
                    references.append({k:source[k] for k in ('url','resolved_url','retrieved_at','sha256') if k in source})
        selected['source-references.json']=rr.encode(references)
        ticket=rr.read_json(directory/'ticket.json')
        if ticket.get('local_snapshot'):
            raise Failure('local_snapshot_publication','Commit and review the public revision before publication',4)
        if ticket.get('pr'):
            metadata=github('repos/'+ticket['repository'])
            if metadata.get('private'):raise Failure('private_evidence','Private PR reports are local by default',4)
        else:
            raise Failure('public_target_required','Publish review evidence for a public PR target',4)
    elif record['kind']=='verify':
        selected['verification.json']=rr.read_artifact(directory,'remote/verification.json')
    else:raise Failure('unsupported_evidence','Only review and proof verification records are publishable',4)
    files={};transformations=[]
    for name,raw in selected.items():
        published=redact(raw,root)
        files[name]=published
        transformations.append({'path':name,'original_sha256':rr.digest(raw),'published_sha256':rr.digest(published),
                                'transformation':'operator paths redacted' if raw!=published else 'unchanged'})
    files['redactions.json']=rr.encode({'schema_version':'fc.public-export.v1','files':transformations,
       'omitted':'Raw snapshots, complete source documents, invocation events, credentials, and execution logs stay local.',
       'limit':'Published reports retain original artifact references; omitted bytes cannot be replayed from this public projection.'})
    files['manifest.json']=rr.encode({'schema_version':'fc.evidence-bundle.v1','run_id':record['id'],
       'kind':record['kind'],'producer':record.get('producer','local_operator'),'artifacts':rr.descriptors(files)})
    target=directory/'public'
    if target.exists():
        existing=rr.collect(target,'public')
        if existing!={'public/'+k:v for k,v in files.items()}:raise Failure('changed_public_export','Existing public export differs; retain the original run',3)
    else:rr.write_directory(target,files)
    return files,record

def publish(root,directory,cfg,dry_run=False):
    files,record=export(root,directory)
    if dry_run:return {'outcome':'pass','public_export':str(directory/'public'),'artifacts':rr.descriptors(files)}
    destination=cfg.get('evidence')
    if not isinstance(destination,dict):raise Failure('missing_evidence_destination','Configure the existing evidence branch',4)
    repo,branch=destination['repository'],destination['branch']
    if not re.fullmatch(r'[\w.-]+/[\w.-]+',repo):raise Failure('invalid_destination','Invalid evidence repository')
    metadata=github('repos/'+repo)
    if metadata.get('private'):raise Failure('private_destination','Public export requires a public evidence destination',4)
    prefix='runs/'+record['id']
    with tempfile.TemporaryDirectory(prefix='fc-evidence-') as temp:
        checkout=Path(temp)/'archive'
        command(['git','clone','--single-branch','--depth','1','--branch',branch,f'https://github.com/{repo}.git',checkout])
        target=checkout/prefix
        if target.exists():
            if rr.collect(target,'bundle')!={'bundle/'+k:v for k,v in files.items()}:
                raise Failure('immutable_run_conflict','Published run path already contains different bytes',3)
        else:
            rr.write_directory(target,files)
            index_path=checkout/'toolkit-index.json'
            index=rr.read_json(index_path) if index_path.exists() else {'schema_version':'fc.evidence-index.v1','runs':[]}
            if index.get('schema_version')!='fc.evidence-index.v1':raise Failure('invalid_index','Unsupported evidence index')
            entry={'id':record['id'],'kind':record['kind'],'created_at':record['created_at'],
                   'outcome':record['outcome'],'producer':record.get('producer','local_operator'),
                   'path':prefix,'manifest_sha256':rr.digest(files['manifest.json']),'target':record.get('target')}
            if record['kind']=='review':
                entry['scope']=rr.read_json(directory/'input/request.json')['scope']
            entry['url']=f'https://github.com/{repo}/tree/{quote(branch,safe="")}/{prefix}'
            index['runs'].append(entry);save(index_path,index)
            git(checkout,'add','--',prefix,'toolkit-index.json')
            git(checkout,'commit','-m','Archive contribution evidence '+record['id'])
            # A concurrent push is rejected, never overwritten. Retrying rechecks immutable bytes.
            git(checkout,'push','origin','HEAD:'+branch)
        revision=git(checkout,'rev-parse','HEAD').decode().strip()
    url=f'https://github.com/{repo}/tree/{revision}/{prefix}'
    result={'outcome':'pass','repository':repo,'branch':branch,'commit':revision,'path':prefix,'url':url,
            'manifest_sha256':rr.digest(files['manifest.json'])}
    # Confirm the archive is retrievable before advertising a durable link.
    if github(f'repos/{repo}/commits/{revision}').get('sha')!=revision:raise Failure('archive_unavailable','Archive commit cannot be retrieved',3)
    save(directory/'publication.json',result)
    return result

def post(directory,publication):
    ticket=rr.read_json(directory/'ticket.json');record=rr.read_json(directory/'run.json')
    repo,number=ticket['repository'],ticket['pr']
    if not number:raise Failure('no_pr','A PR target is required for --post')
    def current():
        pr=github(f'repos/{repo}/pulls/{number}')
        return pr['state']=='open' and pr['head']['sha']==ticket['head'] and pr['base']['sha']==ticket['base']
    if not current():raise Failure('stale_target','Evidence is archived; PR head or base changed, so the summary was not posted',4)
    report=rr.read_json(directory/'bundle/report.json')
    body=f"{MARKER}\n**Advisory FC review — {rr.escape(report['semantic_verdict'])}**\n\n"
    body+=f"Reviewed `{ticket['head']}` against `{ticket['base']}`. Coverage: {report['completeness']}. "
    body+='Produced by a local operator. Maintainers decide acceptance.\n\n'
    for finding in report['review']['findings'][:20]:
        body+=f"- {rr.escape(finding['file'])}:{finding['line']} — {rr.escape(finding['message'][:1500])}\n"
    body+=f"\n[Archived report and evidence provenance]({publication['url']}). Raw source documents and private artifacts are omitted.\n"
    body+=f"\n<!-- fc-review-order: {record['created_at']} {record['id']} -->"
    comments=[]
    for page in range(1,101):
        batch=github(f'repos/{repo}/issues/{number}/comments?per_page=100&page={page}');comments+=batch
        if len(batch)<100:break
    else:raise Failure('comment_limit','Comment pagination limit exceeded',3)
    login=github('user')['login']
    existing=[c for c in comments if c['user']['login']==login and c['body'].startswith(MARKER)]
    if len(existing)>1:raise Failure('comment_conflict','Multiple advisory comments need reconciliation',4)
    if existing:
        order=re.search(r'<!-- fc-review-order: (\S+) (\S+) -->',existing[0]['body'])
        if order and order.group(1)>record['created_at']:raise Failure('older_request','A newer request already has an advisory summary',4)
    if not current():raise Failure('stale_target','PR changed before posting; archive remains available',4)
    endpoint=f'repos/{repo}/issues/comments/{existing[0]["id"]}' if existing else f'repos/{repo}/issues/{number}/comments'
    with tempfile.NamedTemporaryFile(mode='w',suffix='.json') as f:
        json.dump({'body':body},f);f.flush()
        gh('api',endpoint,'--method','PATCH' if existing else 'POST','--input',f.name)
