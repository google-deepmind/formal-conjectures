"""Prepare review inputs and validate reports supplied by an existing agent or human."""
import json
import os
import re
import shutil
import tempfile
import subprocess
import uuid
from pathlib import Path
from . import report as rr, sources, execution as ex
from .core import Failure, command, git, github, save, now, finish

SKILL = Path(__file__).parent/'resources/review'

def skill_path():
    if SKILL.is_dir(): return SKILL
    return Path(__file__).resolve().parents[2]/'.agents/skills/formal-conjectures-review'

def snapshot(root, base):
    """Create an unattached commit using a separate index; never edit the user's index or branch."""
    with tempfile.TemporaryDirectory(prefix='fc-index-') as temp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temp)/'index'))
        git(root, 'read-tree', 'HEAD', env=env)
        git(root, 'add', '-u', '--', '.', env=env)
        tracked = git(root, 'ls-files', '--cached', '-z').decode().split('\0')
        untracked = git(root, 'ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')
        included = sorted({p for p in tracked if p and (root/p).exists()} |
                          {p for p in untracked if p.startswith('FormalConjectures/') and p.endswith('.lean')})
        for name in included:
            if (root/name).is_symlink(): raise Failure('unsupported_scope', 'Symlink input files are unsupported')
        if included:
            git(root, 'add', '--pathspec-from-file=-', '--pathspec-file-nul',
                input=('\0'.join(included)+'\0').encode(), env=env)
        tree = git(root, 'write-tree', env=env).decode().strip()
        head = git(root, 'rev-parse', 'HEAD').decode().strip()
        if tree == git(root, 'rev-parse', 'HEAD^{tree}').decode().strip(): return head, False
        env.update(GIT_AUTHOR_NAME='FC local snapshot', GIT_AUTHOR_EMAIL='local@invalid',
                   GIT_COMMITTER_NAME='FC local snapshot', GIT_COMMITTER_EMAIL='local@invalid')
        commit = git(root, 'commit-tree', tree, '-p', head, input=b'Local contribution snapshot\n', env=env).decode().strip()
        return commit, True

def prepare(root, directory, *, base='origin/main', pr=None, repository=None, supplied=None, collect_sources=True):
    checkout = directory/'checkout'
    base_ref = base
    workspace_head = None if pr else git(root, 'rev-parse', 'HEAD').decode().strip()
    if pr:
        repository = repository or 'google-deepmind/formal-conjectures'
        detail = github(f'repos/{repository}/pulls/{pr}')
        head, base = detail['head']['sha'], detail['base']['sha']
        command(['git', 'init', checkout])
        git(checkout, 'fetch', '--no-tags', f'https://github.com/{repository}.git',
            f'+refs/pull/{pr}/head:refs/review/head', base)
        if git(checkout, 'rev-parse', 'refs/review/head').decode().strip() != head:
            raise Failure('stale_target', 'PR changed while preparing review')
        git(checkout, 'checkout', '--detach', head)
        local = False
    else:
        repository = repository or git(root, 'remote', 'get-url', 'origin').decode().strip()
        head, local = snapshot(root, base)
        base = git(root, 'rev-parse', base).decode().strip()
        # A temporary worktree of the detached snapshot is never checked out in the user's branch.
        git(root, 'worktree', 'add', '--detach', checkout, head)
    try:
        merge = git(checkout, 'merge-base', base, head).decode().strip()
        scope = git(checkout, 'diff', '--name-only', '--no-renames', '-z', merge, head).decode().rstrip('\0').split('\0')
        if not scope or scope == ['']: raise Failure('empty_scope', 'No changed files against the selected base')
        try: ex.build_targets(scope, checkout)
        except rr.InputError as error: raise Failure('unsupported_scope', str(error), 4) from error
        (directory/'sources').mkdir(exist_ok=True)
        collection = sources.collect(directory/'sources', [(checkout/p).read_bytes() for p in scope], supplied) if collect_sources else {'coverage':'incomplete','mode':'not_requested','records':[]}
        files = rr.prepare(checkout, repository, base, skill_path(), directory/'sources', [])
        rr.write_directory(directory/'input', files)
        ticket = {'repository': repository, 'pr': pr, 'head': head, 'base': base,
                  'local_snapshot': local, 'source_collection': collection,
                  'producer': 'local_operator', 'base_ref': base_ref,
                  'workspace_head': workspace_head, 'tree': git(checkout, 'rev-parse', 'HEAD^{tree}').decode().strip()}
        save(directory/'ticket.json', ticket)
        return ticket
    finally:
        if not pr: git(root, 'worktree', 'remove', '--force', checkout)

def load(directory):
    request, files = rr.load_request(directory/'input')
    ticket = rr.read_json(directory/'ticket.json')
    if (ticket['head'] != request['head_commit'] or ticket['base'] != request.get('base_tip')
            or ticket['repository'] != request['repository']):
        raise Failure('input_binding_mismatch', 'Review ticket differs from the retained request', 3)
    return request, files, ticket


def restore(directory, destination):
    """Reconstruct every execution from the retained request, never agent-edited scratch."""
    rr.restore(directory/'input', destination)
    # These are evaluation keys, not candidate inputs for semantic review. The original
    # archive remains intact; execution and agent-facing copies omit the keys.
    for path in list(destination.glob('**/skills/*/evals')):
        if path.is_dir(): shutil.rmtree(path)


def check_environment(image, snapshot):
    if not image:
        raise Failure('missing_image', 'Configure a pinned review image; see conjectures doctor', 4)
    ex.container_args(image, snapshot)  # Validate the pin before invoking Docker.
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml'):
        expected = ex.run('docker', 'run', '--rm', '--network=none', '--entrypoint=cat',
                          image, '/opt/review-cache/'+name)
        if (snapshot/name).read_bytes() != expected:
            raise Failure('environment_mismatch', 'Review image differs from target: '+name, 4)


def build_status(receipt):
    if receipt.get('status') == 'not_run': return 'not_run'
    code = receipt['exit_code']
    return 'pass' if code == 0 else ('error' if code is None or code in (124,125,126,127,137) or code < 0 else 'fail')


def build(directory, configuration):
    """Produce a controller-owned receipt in a fresh container without model access."""
    request, _, _ = load(directory)
    image = configuration.get('image')
    with tempfile.TemporaryDirectory(prefix='fc-build-', dir=directory) as temp:
        snapshot_dir = Path(temp)/'snapshot'
        restore(directory, snapshot_dir)
        targets = ex.build_targets(request['scope'], snapshot_dir)
        receipt = {'command': ['lake','--wfail','build',*targets], 'exit_code': None}
        try:
            check_environment(image, snapshot_dir)
            container = ex.isolated(image, snapshot_dir)
            try:
                receipt = ex.execute(container, receipt['command'], configuration['limits']['build_seconds'])
            finally:
                ex.run('docker', 'rm', '-f', container)
        except Failure as error:
            receipt.update(status='not_run', reason=error.reason, output=str(error))
        except (OSError, subprocess.SubprocessError, rr.InputError) as error:
            receipt.update(status='error', reason='build_environment_error', output=str(error))
    receipt.update(request_id=request['id'], image=image, targets=targets, policy='scoped-build.v1')
    path = directory/'controller/build.json'
    save(path, receipt)
    return build_status(receipt), receipt


def handoff(directory, configuration, record):
    request, files, ticket = load(directory)
    status, receipt = build(directory, configuration)
    # A readable copy is for the existing session. Execution always restores the archive.
    snapshot_dir = directory/'snapshot'
    restore(directory, snapshot_dir)
    for name, raw in files.items():
        if name.startswith(('procedure/', 'sources/')):
            path = snapshot_dir/name; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)
    template = rr.read_json(directory/'input/review-template.json')
    template['reviewer'] = 'REPLACE with human or agent identity; model unknown if unavailable'
    save(directory/'review-template.json', template)
    save(directory/'review.json', template)
    record.update(status='awaiting_review', outcome='incomplete', reason='awaiting_review',
        request_id=request['id'], target=ticket, build_status=status,
        build_receipt_sha256=rr.digest((directory/'controller/build.json').read_bytes()),
        reviewer_metadata={'attribution':'operator_reported', 'model':None, 'usage':None,
                           'context':'Existing session; no claim of blinded or isolated model execution.'},
        paths={name:str(directory/path) for name,path in {
            'request':'input/request.json', 'snapshot':'snapshot', 'sources':'input/sources',
            'procedure':'input/procedure/SKILL.md', 'template':'review-template.json', 'draft':'review.json',
            'build_receipt':'controller/build.json'}.items()},
        next_action=f"Read the procedure and inputs, fill {directory/'review.json'}, then run conjectures review finish {record['id']}.")
    save(directory/'run.json', record)
    return record


def replay(retained, directory):
    request, files, ticket = load(retained)
    files['request.json'] = rr.encode(request)
    # Templates are conveniences, not part of the content-addressed request.
    template = rr.read_json(retained/'input/review-template.json')
    files['review-template.json'] = rr.encode(template)
    rr.write_directory(directory/'input', files)
    save(directory/'ticket.json', ticket)
    return ticket


def bound_receipt(directory, record):
    request, _, _ = load(directory)
    if request['id'] != record.get('request_id'):
        raise Failure('input_binding_mismatch', 'Run belongs to a different request', 3)
    raw = rr.read_artifact(directory, 'controller/build.json')
    receipt = rr.parse(raw)
    if rr.digest(raw) != record['build_receipt_sha256'] or receipt['request_id'] != request['id']:
        raise Failure('changed_build_receipt', 'Independent build receipt changed after preparation', 3)
    return receipt


def require_pending(record):
    if record.get('kind') != 'review' or record.get('status') != 'awaiting_review':
        raise Failure('review_not_pending', 'Use an awaiting_review run; completed reports are immutable', 4)


def bounded_files(folder, prefix):
    # Bound before reading, and reject links through the shared artifact reader.
    if not folder.is_dir() or folder.is_symlink():
        raise Failure('invalid_evidence', 'Expected a plain directory')
    result = {}; size = 0
    for path in sorted(folder.rglob('*')):
        if path.is_symlink(): raise Failure('invalid_evidence', 'Evidence and scratch files cannot be symlinks')
        if not path.is_file(): continue
        size += path.stat().st_size
        if size > 8*1024*1024 or len(result) >= 100:
            raise Failure('evidence_limit', 'At most 100 files and 8 MiB of supplied evidence are supported', 4)
        name = path.relative_to(folder).as_posix()
        result[prefix+'/'+name] = rr.read_artifact(folder, name)
    return result


def scratch(directory, configuration, record, arguments, supplied=None):
    require_pending(record)
    receipt = bound_receipt(directory, record)
    if not arguments: raise Failure('missing_command', 'Supply a command after --')
    evidence_dir = directory/'scratch'
    count = len(list(evidence_dir.glob('*.json'))) if evidence_dir.exists() else 0
    if count >= configuration['limits']['scratch_calls']:
        raise Failure('scratch_limit', 'This run reached its scratch execution limit', 4)
    scratch_files = bounded_files(supplied, 'scratch') if supplied else {}
    with tempfile.TemporaryDirectory(prefix='fc-scratch-', dir=directory) as temp:
        snapshot_dir = Path(temp)/'snapshot'
        restore(directory, snapshot_dir)
        _, files, _ = load(directory)
        for name, raw in files.items():
            if name.startswith(('procedure/', 'sources/')):
                path=snapshot_dir/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(raw)
        for name, raw in scratch_files.items():
            path=snapshot_dir/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(raw)
        image = receipt['image']  # Keep the prepared environment even if local config changes.
        check_environment(image, snapshot_dir)
        container = ex.isolated(image, snapshot_dir)
        try: result = ex.execute(container, arguments, configuration['limits']['scratch_seconds'])
        finally: ex.run('docker', 'rm', '-f', container)
    identity = uuid.uuid4().hex
    result.update(request_id=record['request_id'], image=image, producer='local_operator',
                  purpose='scratch_only', inputs=rr.descriptors(scratch_files))
    save(evidence_dir/(identity+'.json'), result)
    # Preserve witness bytes as well as output; they never become independent checks.
    if scratch_files: rr.write_directory(evidence_dir/identity, scratch_files)
    return {'outcome':build_status(result), 'run':record['id'],
            'evidence':'evidence/scratch/'+identity+'.json', **result}


def applicability(root, ticket):
    try:
        if ticket.get('pr'):
            detail = github(f"repos/{ticket['repository']}/pulls/{ticket['pr']}")
            current = detail['state']=='open' and detail['head']['sha']==ticket['head'] and detail['base']['sha']==ticket['base']
        elif ticket.get('workspace_head') and ticket.get('tree'):
            head, _ = snapshot(root, ticket['base_ref'])
            current = (git(root,'rev-parse','HEAD').decode().strip()==ticket['workspace_head'] and
                git(root,'rev-parse',head+'^{tree}').decode().strip()==ticket['tree'] and
                git(root,'rev-parse',ticket['base_ref']).decode().strip()==ticket['base'])
        else: return 'unconfirmed'
        return 'current' if current else 'historical'
    except (Failure, OSError, subprocess.SubprocessError):
        return 'unconfirmed'


def complete(root, directory, record, report_path, supplied=None):
    require_pending(record)
    receipt = bound_receipt(directory, record)
    request, _, ticket = load(directory)
    if report_path.stat().st_size > 1024*1024:
        raise Failure('report_limit', 'Review JSON exceeds 1 MiB')
    result = rr.read_json(report_path)
    rr.require(isinstance(result,dict), 'review must be an object')
    if isinstance(result.get('reviewer'), str) and result['reviewer'].startswith('REPLACE'):
        raise Failure('unfinished_review', 'Fill the reviewer identity; use model unknown when necessary', 4)
    # Let the contract validator reject malformed structures before enforcing source coverage.
    evidence = {'evidence/build.json':rr.encode(receipt)}
    if (directory/'scratch').exists(): evidence |= bounded_files(directory/'scratch', 'evidence/scratch')
    if supplied: evidence |= bounded_files(supplied, 'evidence/operator')
    _, inputs = rr.load_request(directory/'input')
    rr.validate_review(result, request, inputs | evidence)
    if ticket['source_collection']['coverage'] == 'incomplete':
        result['coverage']['source-fidelity'] = 'incomplete'
    status = build_status(receipt)
    manifest = {'request_id':request['id'], 'artifacts':rr.descriptors(evidence), 'checks':[{
        'kind':'build', 'status':status, 'producer':record.get('producer','local_operator'),
        'policy':'scoped-build.v1', 'detail':'Independent isolated build; no proof verification.',
        'evidence':['evidence/build.json']}]}
    # Stage and validate everything before changing a pending run. Supplied checks.json
    # is ordinary operator evidence and never selects a check policy or verdict.
    with tempfile.TemporaryDirectory(prefix='fc-complete-', dir=directory) as temp:
        staging = Path(temp)
        save(staging/'review.json',result)
        rr.write_directory(staging/'evidence', evidence | {'checks.json':rr.encode(manifest)})
        bundle = rr.assemble(directory/'input',directory/'input',staging/'review.json',staging/'evidence')
        report = rr.parse(bundle['report.json'])
        state = applicability(root,ticket)
        observation = rr.parse(bundle['observation.json'])
        observation.update(current_request_id=None, freshness={'current':'current','historical':'STALE','unconfirmed':'unconfirmed'}[state],
                           observed_at=now(), scope='Target head/base only; retained procedure and sources remain frozen.')
        if state!='current': observation['completeness']='incomplete'
        bundle['observation.json']=rr.encode(observation)
        bundle['summary.md']=rr.render(report,observation).encode()
        rr.write_directory(staging/'bundle',bundle)
        for name in ('review.json','evidence','bundle'):
            if name != 'review.json' and (directory/name).exists(): raise Failure('existing_completion', 'Retain existing completion artifacts and start a new run', 3)
        for name in ('review.json','evidence','bundle'): (staging/name).rename(directory/name)
    outcome = 'error' if status=='error' else ('fail' if status=='fail' or report['semantic_verdict']=='NEEDS REVISION'
        else ('incomplete' if report['gaps'] or state!='current' else 'pass'))
    record.pop('reason',None)
    reason = ('build_execution_error' if status=='error' else 'build_failed' if status=='fail' else
              'semantic_findings' if report['semantic_verdict']=='NEEDS REVISION' else
              'target_changed' if state=='historical' else 'freshness_unconfirmed' if state=='unconfirmed' else
              'coverage_incomplete' if report['gaps'] else 'review_complete')
    return finish(directory,record,outcome,reason=reason,coverage=report['review']['coverage'],gaps=report['gaps'],
        applicability=state, reviewer=result['reviewer'], report=str(directory/'bundle/summary.md'),
        next_action='Inspect the report. Publish only with explicit authorization.')
