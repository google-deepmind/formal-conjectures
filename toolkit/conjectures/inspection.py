"""Local checks and bounded log inspection, separate from semantic review scope."""
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
    print('Building '+', '.join(targets)+'…',file=sys.stderr)
    try:
        with (directory/'build.log').open('wb') as output:
            proc=subprocess.run(['lake','--wfail','build',*targets],cwd=root,stdout=output,stderr=subprocess.STDOUT,
                                timeout=cfg['limits']['build_seconds'])
        return finish(directory,record,'pass' if proc.returncode==0 else 'fail',exit_code=proc.returncode,
                      next_action='Read build output: conjectures run logs '+record['id'])
    except BaseException as error:
        finish(directory,record,'cancelled' if isinstance(error,KeyboardInterrupt) else 'error',reason='interrupted' if isinstance(error,KeyboardInterrupt) else 'build_execution_error')
        raise
