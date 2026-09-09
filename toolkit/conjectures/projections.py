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
