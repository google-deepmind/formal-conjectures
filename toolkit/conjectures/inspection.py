"""Local checks and bounded log inspection, separate from semantic review scope."""
from .ui import stage, log_location
import subprocess
from pathlib import Path
from . import report as rr
from .core import Failure, finish, start_run


def logs(directory, record, artifact=None):
    if artifact:
        rr.relative(artifact)
        paths=[directory/artifact]
        if paths[0].resolve().is_relative_to(directory.resolve()) is False:
            raise Failure('invalid_artifact','Artifact must be inside this run.')
    else:
        paths=sorted(directory.rglob('*.log'))
        paths += [p for p in [directory/'controller/build.json', *sorted((directory/'scratch').glob('*.json'))] if p.is_file()]
    result=[]
    for path in paths[:30]:
        if path.is_symlink() or not path.is_file():
            if artifact:raise Failure('invalid_artifact','Choose a retained regular file inside this run.')
            continue
        if not path.resolve().is_relative_to(directory.resolve()):continue
        with path.open('rb') as stream:raw=stream.read(1024*1024)
        text=raw.decode('utf-8',errors='replace')
        if path.suffix=='.json':
            try:
                value=rr.parse(raw)
                if isinstance(value,dict) and 'output' in value:text=str(value['output'])
            except ValueError:pass
        if path.stat().st_size>len(raw):text+='\n[Output truncated at 1 MiB]'
        result.append({'path':str(path.relative_to(directory)),'text':text})
    return {'outcome':'pass','run':record,'logs':result}


def check_targets(root, paths):
    from .execution import build_targets
    shared=[p for p in paths if p.startswith(('FormalConjecturesUtil','FormalConjecturesForMathlib','FormalConjectures/Util/','FormalConjectures/Subsets/')) or p in ('lakefile.toml','lake-manifest.json','lean-toolchain')]
    if shared:
        raise Failure('unsupported_check_scope','Shared/configuration changes: '+', '.join(shared[:8])+'. Use lake --wfail build FormalConjecturesForMathlib and lake --wfail test; dependency changes need the full hosted build.',4)
    lean=[p for p in paths if p.endswith('.lean')]
    # Build is independent of the five-module semantic-review limit.
    targets=[]
    for path in lean:targets.extend(build_targets([path],root))
    return targets


def check_local(root, paths, cfg):
    targets=check_targets(root,paths)
    if not targets:return {'outcome':'pass','reason':'no_changed_modules','message':'No changed Lean modules to build.'}
    directory,record=start_run(root,'check',targets=targets)
    import sys
    stage('Building '+', '.join(targets));log_location(directory/'build.log')
    try:
        with (directory/'build.log').open('wb') as output:
            proc=subprocess.run(['lake','--wfail','build',*targets],cwd=root,stdout=output,stderr=subprocess.STDOUT,
                                timeout=cfg['limits']['build_seconds'])
        return finish(directory,record,'pass' if proc.returncode==0 else 'fail',exit_code=proc.returncode,
                      next_action='Read build output: conjectures run logs '+record['id'])
    except BaseException as error:
        finish(directory,record,'cancelled' if isinstance(error,KeyboardInterrupt) else 'error',reason='interrupted' if isinstance(error,KeyboardInterrupt) else 'build_execution_error')
        raise


def show(root, directory, record, *, refresh=True):
    """Read the case evidence; freshness is a separate, explicitly timed observation."""
    value = dict(record)
    if record['kind'] == 'review':
        path = directory/'bundle/report.json'
        if path.is_file():
            report = rr.read_json(path)
            rr.require(report.get('schema_version') == rr.REPORT_VERSION, 'Unsupported review report')
            value['review_summary'] = {k:report[k] for k in ('semantic_verdict','completeness','checks','gaps')}
            value['review_summary'].update({k:report['review'].get(k,[]) for k in
                                            ('findings','questions','reconciliations','coverage','reviewer')})
            value['evidence_paths'] = ['bundle/report.json','bundle/observation.json','bundle/summary.md']
        attribution=directory/'evidence/operator/reviewer-attributions.json'
        if attribution.is_file():value['reviewer_attributions']=rr.read_json(attribution)
        if refresh and record.get('target'):
            from .review import observe
            value['current_observation'] = observe(root,record['target'])
            value['current_applicability'] = value['current_observation']['applicability']
    if record['kind'] == 'verify' and record.get('result'):
        result = record['result'];comparator = result.get('comparator') or {}
        value['verification_summary'] = {k:result.get(k) for k in ('outcome','reason','detail','pins','producer','semantic_assessment_required')}
        value['verification_summary'].update(stage=comparator.get('stage'),
            policy_reason=comparator.get('reason'), policy_outcome=comparator.get('outcome') if comparator.get('outcome') in ('pass','rejected') else 'not_evaluated')
        value['evidence_paths'] = ['remote/verification.json']
    value['next_action'] = next_action(value)
    return value


def next_action(record):
    identity = record['id']
    if record['status'] == 'awaiting_review':return 'Complete review draft: conjectures review finish '+identity
    if record['kind'] == 'verify' and record['status'] in ('queued','in_progress','running','cancellation_requested'):
        return 'Retrieve verification: conjectures run wait '+identity
    if record.get('current_applicability') == 'historical':return 'Inputs changed. Prepare a new review; retain this result as history.'
    if record.get('outcome') == 'pass' and (record.get('verification_summary') or record.get('result') or {}).get('semantic_assessment_required'):
        return 'Arrange semantic assessment of the submitted definitions against the source. Kernel verification alone does not establish their intended meaning.'
    if record.get('verification_summary') and record.get('outcome') in ('fail','error','incomplete'):
        return 'Inspect verifier logs: conjectures run logs '+identity+'\nResolve the reported cause before starting a new verification.'
    if record.get('review_summary') and record.get('outcome') in ('fail','error','incomplete'):
        target=record.get('target') or {}
        return 'Address the findings and missing coverage, then prepare a new review: conjectures review '+('--pr '+str(target['pr']) if target.get('pr') else '--changed')
    if record.get('outcome') in ('fail','error','incomplete'):return 'Inspect findings and coverage: conjectures run show '+identity
    return record.get('next_action') or 'Inspect retained evidence: conjectures run show '+identity
