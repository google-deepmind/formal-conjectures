"""Exact joins for website and board consumers. No status inference from log text."""
from . import report as rr
from .catalog_data import module_path,repository_name

def evidence_for(problem,index,source_revision=None,source_repository=None):
    result=[]
    for run in index.get('runs',[]):
        target=run.get('target') or {}
        if source_repository and repository_name(target.get('repository'))!=repository_name(source_repository):continue
        if run.get('kind')=='verify':
            try:same_module=module_path(target.get('module',''))==module_path(problem['module'])
            except ValueError:same_module=False
            if target.get('declaration')!=problem['theorem'] or not same_module:continue
            revision=target.get('commit')
        else:
            path=problem.get('githubPath')
            if not path or path not in run.get('scope',[]):continue
            revision=target.get('head')
        state='unconfirmed' if not source_revision or not source_repository else ('current' if revision==source_revision else 'historical')
        result.append({**run,'applicability':state,'applies_to_revision':revision})
    return sorted(result,key=lambda r:r['created_at'],reverse=True)

def review_projection(report):
    """The board keeps its own queue/timing model and reads this advisory result."""
    if report.get('schema_version')!=rr.REPORT_VERSION:raise ValueError('Unsupported review report')
    return {'request_id':report['request']['id'],'repository':report['request']['repository'],
            'head_commit':report['request']['head_commit'],'base_tip':report['request'].get('base_tip'),
            'semantic_verdict':report['semantic_verdict'],'completeness':report['completeness'],
            'coverage':report['review']['coverage'],'findings':report['review']['findings'],
            'checks':report['checks'],'gaps':report['gaps'],'authority_effect':'none'}


def work_context(value):
    """A descriptive open-work snapshot; queue classification remains in queueboard."""
    rr.require(isinstance(value,dict) and value.get('schema_version')=='fc.work-context.v1','Unsupported work context')
    rr.require(bool(repository_name(value.get('repository'))),'Missing work repository')
    rr.text(value.get('observed_at'),'work observation time')
    rr.array(value.get('pull_requests'),'open pull requests')
    seen=set()
    for pr in value['pull_requests']:
        rr.require(isinstance(pr,dict),'Each work item must be a PR object')
        rr.require(type(pr.get('number')) is int and pr['number']>0 and pr['number'] not in seen,'Invalid or duplicate PR')
        seen.add(pr['number']);rr.text(pr.get('title'),'PR title')
        rr.array(pr.get('files'),'PR paths')
        for path in pr['files']:rr.relative(path)
        for key in ('head','base'):
            if pr.get(key) is not None:
                import re
                rr.require(re.fullmatch('[0-9a-f]{40}',pr[key]) is not None,'Invalid PR revision')
        pr['url']=f"https://github.com/{repository_name(value['repository'])}/pull/{pr['number']}"
    return value


def contribution_context(index, work=None):
    work=work_context(work) if work else None
    records=[]
    for run in index.get('runs',[]):
        rr.require(run.get('validation')=='validated_bundle','Only validated evidence can be projected')
        target=run.get('target') or {};state='unconfirmed';changes=[]
        pr=next((p for p in work['pull_requests'] if p['number']==target.get('pr')),None) if work and repository_name(target.get('repository'))==repository_name(work['repository']) else None
        if pr and pr.get('head') and pr.get('base'):
            changes=[key+'_changed' for key in ('head','base') if target.get(key)!=pr[key]]
            state='historical' if changes else 'current'
        records.append({**run,'applicability':state,'changes':changes,
                        'applicability_observed_at':work['observed_at'] if work else None})
    return {**index,'schema_version':'fc.contribution-context.v1','runs':records,
            'pull_requests':work['pull_requests'] if work else [],'work_context':work,
            'authority_effect':'none'}


def main():
    import argparse
    from .evidence_reader import load
    from .core import save
    parser=argparse.ArgumentParser(description='Validate evidence and project shared FC contribution records.')
    parser.add_argument('--repository');parser.add_argument('--branch')
    parser.add_argument('--work',type=__import__('pathlib').Path)
    parser.add_argument('--out',required=True,type=__import__('pathlib').Path)
    args=parser.parse_args()
    if bool(args.repository)!=bool(args.branch):parser.error('Use --repository and --branch together')
    index=load(destination={'repository':args.repository,'branch':args.branch} if args.repository else None)
    result=contribution_context(index,rr.read_json(args.work) if args.work else None)
    save(args.out,result)
    # Unavailable feeds are visible without destroying unrelated queue information.
    return 0


if __name__=='__main__':raise SystemExit(main())
