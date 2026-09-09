"""One interface for FC contribution review and exact-target proof workspaces."""
import argparse
import json
import importlib.util
import os
import shutil
import subprocess
import sys
from pathlib import Path
from . import __version__, report as rr
from .core import Failure, command, config, finish, run_dir, runs, save, start_run, workspace, run_lock

EXIT = {'pass':0, 'fail':1, 'incomplete':4, 'error':3, 'cancelled':5}

class ArgumentParser(argparse.ArgumentParser):
    def error(self,message):
        if '--json' in sys.argv:
            print(json.dumps({'outcome':'error','reason':'invalid_arguments','message':message}))
            raise SystemExit(2)
        super().error(message)

def parser():
    p = ArgumentParser(prog='conjectures',description=__doc__)
    p.add_argument('--version',action='version',version=__version__)
    p.add_argument('--json',action='store_true',help='Emit structured output; progress remains on stderr')
    sub = p.add_subparsers(dest='command',required=True)
    def cmd(name, help):
        q = sub.add_parser(name,help=help,description=help)
        q.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
        return q
    cmd('doctor','Check FC tools, executor configuration, and pins without AI credentials')
    for name in ('find','show'):
        q=cmd(name,'Search the catalog' if name=='find' else 'Show statements, variants, sources, and evidence')
        q.add_argument('target');q.add_argument('--catalog',type=Path)
    q=cmd('check','Build changed modules')
    group=q.add_mutually_exclusive_group(required=True)
    group.add_argument('--changed',action='store_true');group.add_argument('--pr',type=int)
    group.add_argument('file',nargs='?')
    q.add_argument('--base',default='origin/main');q.add_argument('--repository')
    q=cmd('review','Prepare inputs and complete a review in your existing agent session')
    r=q.add_subparsers(dest='operation',required=True)
    s=r.add_parser('prepare',help='Freeze inputs and build; leave the run awaiting semantic review')
    s.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
    group=s.add_mutually_exclusive_group(required=True)
    group.add_argument('--changed',action='store_true');group.add_argument('--pr',type=int)
    group.add_argument('--input',type=Path,help='Replay a retained run with a new independent build')
    s.add_argument('--base',default='origin/main');s.add_argument('--repository');s.add_argument('--sources',type=Path)
    s=r.add_parser('finish',help='Validate an existing agent or human report and retain the result')
    s.add_argument('run');s.add_argument('--report',type=Path,required=True)
    s.add_argument('--evidence',type=Path,help='Supporting files, retained under evidence/operator/')
    s.add_argument('--post',action='store_true',help='Explicitly archive public evidence, then post its advisory PR summary')
    s.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
    s=r.add_parser('exec',help='Run an optional scratch check in a fresh isolated container')
    s.add_argument('--files',type=Path,help='Witness files copied under /tmp/work/scratch/')
    s.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
    s.add_argument('run');s.add_argument('arguments',nargs=argparse.REMAINDER,help='Command after --; options precede RUN')
    q=cmd('init','Generate a pinned proof workspace for one exact declaration')
    q.add_argument('target');q.add_argument('--out',required=True,type=Path)
    q.add_argument('--source-ref',default='origin/main');q.add_argument('--repository')
    q.add_argument('--catalog',type=Path)
    q=cmd('verify','Verify a committed public proof workspace on qualified Linux')
    q.add_argument('directory',type=Path)
    cmd('status','Show runs, outcomes, coverage gaps, and the next action')
    q=cmd('run','Inspect local records or control supported remote runs')
    r=q.add_subparsers(dest='operation',required=True)
    for op in ('list','show','logs','wait','cancel'):
        s=r.add_parser(op);s.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
        if op!='list':s.add_argument('run')
    q=cmd('evidence','Publish a validated public export explicitly')
    r=q.add_subparsers(dest='operation',required=True);s=r.add_parser('publish')
    s.add_argument('run');s.add_argument('--post',action='store_true',help='Post an advisory PR summary after archiving');s.add_argument('--dry-run',action='store_true');s.add_argument('--json',action='store_true',default=argparse.SUPPRESS)
    return p

def doctor(root, cfg):
    from .review import skill_path
    tools={name:shutil.which(name) for name in ('git','gh','uv','lake','lean','docker','pdftotext')}
    if os.environ.get('CONJECTURES_GH'): tools['gh']=shutil.which(os.environ['CONJECTURES_GH'])
    gaps=[]
    if not tools['docker']: gaps.append('Install Docker to run isolated contribution checks')
    if not cfg['image']: gaps.append('Configure a pinned review image')
    else:
        from .execution import container_args
        try: container_args(cfg['image'],root)
        except (ValueError,TypeError): gaps.append('Review image must be pinned by SHA-256 digest')
    if (cfg['executor'] or cfg['evidence']) and not tools['gh']:
        gaps.append('Install gh or configure CONJECTURES_GH for GitHub operations')
    if not cfg['executor']: gaps.append('Configure a qualified Linux executor for proof verification')
    return {'outcome':'incomplete' if gaps else 'pass', 'tools':tools, 'configuration':cfg,
            'lean_toolchain':(root/'lean-toolchain').read_text().strip() if (root/'lean-toolchain').is_file() else None,
            'gaps':gaps, 'review_skill':str(skill_path()/'SKILL.md'), 'agent':'Use your existing agent session or write a review manually. No AI credentials are needed by the toolkit.'}

def dispatch(args):
    root=workspace();cfg=config(root)
    if args.command=='doctor':return doctor(root,cfg)
    if args.command in ('find','show'):
        from .catalog import load,matches
        data=load(root,args.catalog);found=matches(data,args.target)
        return {'outcome':'pass' if found else 'incomplete','problems':found,
                'moduleDocstrings':{p['module']:data.get('moduleDocstrings',{}).get(p['module']) for p in found},
                'coverage_gaps':data.get('coverage_gaps',[]),
                'catalog_note':'Published metadata is descriptive; acceptance and exact-target verification are separate.'}
    if args.command=='status' or (args.command=='run' and args.operation=='list'):
        records=runs(root)
        return {'outcome':'pass','runs':records,'next_action':
                'Complete awaiting_review runs with review finish; inspect outcomes before publishing.' if records else 'Run conjectures doctor, then review prepare or init.'}
    if args.command=='run':
        directory=run_dir(root,args.run);record=rr.read_json(directory/'run.json')
        if args.operation=='show':
            if record['kind']=='review' and record.get('target'):
                from .review import applicability
                return {**record,'current_applicability':applicability(root,record['target'])}
            return record
        if args.operation=='logs':
            return {'outcome':'pass','run':record,'artifacts':[str(p.relative_to(directory)) for p in sorted(directory.rglob('*')) if p.is_file()]}
        if record['kind']=='review':
            if args.operation=='cancel':
                with run_lock(directory):
                    record=rr.read_json(directory/'run.json')
                    from .review import require_pending
                    require_pending(record)
                    return finish(directory,record,'cancelled',reason='operator_cancelled',next_action='Start a new review to continue.')
            return record  # Local review waits for the existing session, not a background model.
        if importlib.util.find_spec('conjectures.proof') is None:
            raise Failure('unavailable_command','Remote run control follows in the proof workspace PR',4)
        from .proof import control
        return control(directory,record,args.operation)
    if args.command=='review':
        from . import review
        if args.operation!='prepare':
            if getattr(args,'post',False) and importlib.util.find_spec('conjectures.evidence') is None:
                raise Failure('unavailable_command','Publication follows in the evidence PR',4)
            directory=run_dir(root,args.run)
            with run_lock(directory):
                record=rr.read_json(directory/'run.json')
                if args.operation=='exec':
                    arguments=args.arguments[1:] if args.arguments[:1]==['--'] else args.arguments
                    return review.scratch(directory,cfg,record,arguments,args.files)
                result=review.complete(root,directory,record,args.report,args.evidence)
                if args.post:
                    from .evidence import publish,post
                    # Publication errors never overwrite a retained semantic review outcome.
                    publication=publish(root,directory,cfg)
                    post(directory,publication)
                    result={**result,'publication':publication}
                return result
        directory,record=start_run(root,'review')
        try:
            print('Preparing exact review inputs…',file=sys.stderr)
            ticket=review.replay(args.input.resolve(),directory) if args.input else review.prepare(
                root,directory,base=args.base,pr=args.pr,repository=args.repository,supplied=args.sources)
            record.update(target=ticket);save(directory/'run.json',record)
            print('Building independently; your existing session will conduct the semantic review…',file=sys.stderr)
            return review.handoff(directory,cfg,record)
        except BaseException as error:
            finish(directory,record,'cancelled' if isinstance(error,KeyboardInterrupt) else 'error',
                   reason=getattr(error,'reason','execution_error'),detail=str(error))
            raise
    if args.command=='check':
        from . import execution as ex
        from .core import git
        if args.pr:
            from . import review
            directory,record=start_run(root,'check')
            try:
                ticket=review.prepare(root,directory,pr=args.pr,repository=args.repository,collect_sources=False)
                outcome,receipt=review.build(directory,cfg)
                return finish(directory,record,'incomplete' if outcome=='not_run' else outcome,target=ticket,receipt=receipt)
            except BaseException as error:
                finish(directory,record,'error',reason=getattr(error,'reason','execution_error'),detail=str(error));raise
        paths=[args.file] if args.file else sorted(set(git(root,'diff','--name-only',args.base).decode().splitlines()+
            [p for p in git(root,'ls-files','--others','--exclude-standard').decode().splitlines() if p.startswith('FormalConjectures/') and p.endswith('.lean')]))
        targets=ex.build_targets(paths,root)
        directory,record=start_run(root,'check',targets=targets)
        proc=subprocess.run(['lake','--wfail','build',*targets],cwd=root,capture_output=True)
        (directory/'build.log').write_bytes(proc.stdout+proc.stderr)
        return finish(directory,record,'pass' if proc.returncode==0 else 'fail',exit_code=proc.returncode)
    if args.command in ('init','verify'):
        if importlib.util.find_spec('conjectures.proof') is None:
            raise Failure('unavailable_command','Proof workspace support is not included in this revision',4)
        from . import proof
        return proof.initialize(root,args,cfg) if args.command=='init' else proof.verify(root,args.directory,cfg)
    if args.command=='evidence':
        if importlib.util.find_spec('conjectures.evidence') is None:
            raise Failure('unavailable_command','Evidence publication is not included in this revision',4)
        from .evidence import publish,post
        if args.dry_run and args.post: raise Failure('invalid_arguments','--post cannot be combined with --dry-run')
        directory=run_dir(root,args.run)
        with run_lock(directory):
            result=publish(root,directory,cfg,args.dry_run)
            if args.post: post(directory,result)
            return result

def main():
    args=parser().parse_args()
    try:
        result=dispatch(args)
        if result is None:return 0
        print(json.dumps(result,ensure_ascii=False,indent=2))
        return EXIT.get(result.get('outcome'),0)
    except (Failure,rr.InputError,OSError,ValueError,subprocess.SubprocessError) as error:
        value={'outcome':'error','reason':getattr(error,'reason','invalid_input'),'message':str(error)}
        print(json.dumps(value) if args.json else value['reason']+': '+value['message'],file=sys.stdout if args.json else sys.stderr)
        return getattr(error,'code',2)
    except KeyboardInterrupt:
        print(json.dumps({'outcome':'cancelled','reason':'interrupted'}));return 5

if __name__=='__main__':
    raise SystemExit(main())
