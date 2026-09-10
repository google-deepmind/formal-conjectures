"""Local configuration, process boundaries, and durable run records."""
import json
import fcntl
import sys
from contextlib import contextmanager
import os
import re
import subprocess
import tempfile
import uuid
from datetime import datetime, timezone
from pathlib import Path
from . import report as rr

class Failure(Exception):
    def __init__(self, reason, message, code=2):
        super().__init__(message)
        self.reason, self.code = reason, code

def now():
    return datetime.now(timezone.utc).isoformat()

def command(args, cwd=None, timeout=120, **kwargs):
    from .ui import diagnostic
    import shlex
    diagnostic(shlex.join([str(x) for x in args]))
    proc = subprocess.run([str(x) for x in args], cwd=cwd, timeout=timeout,
                          capture_output=True, **kwargs)
    if proc.returncode:
        raise Failure('execution_error', proc.stderr.decode(errors='replace')[-6000:], 3)
    return proc.stdout


def logged_command(args, path, *, cwd=None, timeout=1800):
    """Retain download/build diagnostics; terminal output is presentation-owned."""
    from .ui import log_location, diagnostic
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    log_location(path)
    try:
        with path.open('ab') as log:
            subprocess.run([str(x) for x in args],cwd=cwd,stdout=log,stderr=subprocess.STDOUT,
                           check=True,timeout=timeout)
    finally:
        # Verbose output stays bounded even when a dependency build emits megabytes.
        with path.open('rb') as log:
            log.seek(0,2);size=log.tell();log.seek(max(0,size-6000))
            diagnostic(log.read().decode(errors='replace'))


def git(root, *args, **kwargs):
    return command(['git', '-C', root, *args], **kwargs)

def workspace(path=None, required=True, allow_proof=False):
    if allow_proof:
        start=Path(path or Path.cwd()).resolve()
        for directory in (start,*start.parents):
            if (directory/'fc-provenance.json').is_file():return directory
    try:
        root = Path(command(['git', '-C', str(path or Path.cwd()), 'rev-parse', '--show-toplevel']).decode().strip()).resolve()
        if (root/'FormalConjectures').is_dir():
            return root
    except Failure:
        pass
    except FileNotFoundError:
        if required or path is not None:
            raise Failure('missing_tool','Install Git for checkout operations. Browsing and doctor work without Git.',4)
        return None
    if required or path is not None:
        raise Failure('workspace_required', 'Run inside an FC checkout, or use conjectures --repo /path/to/formal-conjectures COMMAND.', 4)
    return None

def user_cache():
    return Path(os.environ.get('XDG_CACHE_HOME', str(Path.home()/'.cache')))/'conjectures'

def config_path(root=None):
    return root/'.conjectures/config.json' if root else Path(os.environ.get('XDG_CONFIG_HOME', str(Path.home()/'.config')))/'conjectures/config.json'

def gh(*args):
    # Use native gh. An operator can select an authenticated wrapper explicitly.
    return command([os.environ.get('CONJECTURES_GH', 'gh'), *args])

def github(path):
    return rr.parse(gh('api', path))

def config(root):
    result = {'catalog_url': None, 'executor': None, 'evidence': None, 'image': None,
              'limits': {'build_seconds': 180, 'scratch_seconds': 60, 'scratch_calls': 20}}
    for p in [config_path(), *([config_path(root)] if root else [])]:
        if p.exists():
            value = rr.read_json(p)
            if not isinstance(value, dict): raise Failure('invalid_configuration', 'Configuration must be an object')
            obsolete = set(value) & {'backend', 'model'}
            if obsolete:
                print('Ignoring obsolete model/backend configuration; your existing agent owns model access.', file=sys.stderr)
                value = {k:v for k,v in value.items() if k not in obsolete}
            if set(value) - set(result):
                raise Failure('invalid_configuration', 'Unknown toolkit configuration field')
            limits = value.pop('limits', {})
            if not isinstance(limits, dict): raise Failure('invalid_configuration', 'Limits must be an object')
            # Old model-time and tool-call bounds cannot constrain an external session.
            limits = {k:v for k,v in limits.items() if k not in ('seconds', 'tools')}
            if set(limits) - set(result['limits']): raise Failure('invalid_configuration', 'Unknown execution limit')
            result['limits'].update(limits)
            result.update(value)
    if result['catalog_url'] is not None:
        from .catalog import catalog_url
        result['catalog_url']=catalog_url(result['catalog_url'])
    if result['image'] is not None and not isinstance(result['image'],str):
        raise Failure('invalid_configuration','image must be a digest string or null.')
    executor_fields=('kind','toolkit','ref','tools') if isinstance(result['executor'],dict) and result['executor'].get('kind')=='linux' else ('kind','repository','ref')
    for name, fields in [('executor', executor_fields), ('evidence', ('repository','branch'))]:
        value=result[name]
        if value is not None and (not isinstance(value,dict) or any(not isinstance(value.get(k),str) or not value[k] for k in fields)):
            raise Failure('invalid_configuration', name+' must include '+', '.join(fields)+' as nonempty strings.')
    for key, ceiling in (('build_seconds',1800), ('scratch_seconds',300), ('scratch_calls',100)):
        if type(result['limits'][key]) is not int or not 0 < result['limits'][key] <= ceiling:
            raise Failure('invalid_configuration', f'{key} must be an integer from 1 to {ceiling}')
    return result

@contextmanager
def run_lock(directory):
    # Serialize completion, scratch execution and cancellation without a daemon.
    with (directory/'operation.lock').open('a') as lock:
        try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Failure('run_busy', 'Another operation is using this run', 4) from error
        try: yield
        finally: fcntl.flock(lock, fcntl.LOCK_UN)


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as f:
        f.write(rr.encode(value)); temp = Path(f.name)
    temp.replace(path)

def start_run(root, kind, **details):
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:12]
    directory = root/'.conjectures/runs'/run_id
    directory.mkdir(parents=True, mode=0o700)
    record = dict(schema_version='fc.toolkit.run.v1', id=run_id, kind=kind,
                  created_at=now(), status='running', outcome=None,
                  producer='local_operator', **details)
    save(directory/'run.json', record)
    return directory, record

def finish(directory, record, outcome, **details):
    record.update(status='completed', outcome=outcome, finished_at=now(), **details)
    save(directory/'run.json', record)
    return record

def run_dir(root, identity, readonly=False):
    records = runs(root)
    if identity == 'latest':
        if not readonly:
            raise Failure('explicit_run_required', 'Use an explicit run ID for this operation; inspect conjectures run list.')
        if not records:
            raise Failure('unknown_run', 'No runs yet. Start with conjectures review --pr NUMBER.')
        identity = records[0]['id']
    elif not re.fullmatch(r'[0-9]{8}T[0-9]{6}Z-[a-f0-9]{12}', identity):
        if not re.fullmatch(r'[0-9a-fTZ-]+', identity):
            raise Failure('invalid_run', 'Use a run ID or unique prefix from conjectures run list.')
        found = [r['id'] for r in records if r['id'].startswith(identity)]
        if len(found) != 1:
            raise Failure('ambiguous_run' if found else 'unknown_run', 'Choose an explicit run ID: '+', '.join(found[:10]) if found else identity)
        identity = found[0]
    path = root/'.conjectures/runs'/identity
    if path.is_symlink() or not (path/'run.json').is_file():
        raise Failure('unknown_run', identity)
    return path

def runs(root):
    return [rr.read_json(p) for p in sorted((root/'.conjectures/runs').glob('*/run.json'), reverse=True)]
