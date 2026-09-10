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
from .interface import parser, parse

EXIT = {'pass':0, 'fail':1, 'incomplete':4, 'error':3, 'cancelled':5}

from .onboarding import doctor


def dispatch(args):
    if args.command=='completion':
        from .interface import completion
        return {'text': completion(args.shell)}
    optional = args.command in ('doctor','find','show') or (args.command=='setup' and args.global_config)
    root=workspace(getattr(args,'repo',None),required=not optional);cfg=config(root)
    if args.command=='doctor':return doctor(root,cfg,args.capability)
    if args.command=='setup':
        from .onboarding import setup
        return setup(root,args)
    if args.command in ('find','show'):
        from .catalog import load,matches
        data=load(root,args.catalog,refresh=args.refresh,offline=args.offline);found=matches(data,args.target)
        source=data.get('provenance',{}).get('source')
        if source:
            from .catalog_data import module_path,source_url
            found=[{**p,'githubPath':module_path(p['module']),'source_url':source_url(source,p['module'])} for p in found]
        if args.command=='show' and not found:raise Failure('unknown_target','No matching target. Try conjectures find QUERY.')
        total=len(found)
        if args.command=='find':found=found[:args.limit]
        if args.command=='show':
            from .catalog import attach_evidence
            found=attach_evidence(found,root,cfg,source,offline=args.offline)
            from . import work
            context=work.load(offline=args.offline) if source else {'status':'unconfirmed','pull_requests':[]}
            found=[{**p,'related_work':work.related(p,context,source),'work_availability':context['status'],
                    'work_observed_at':context.get('observed_at')} for p in found]
        missing=args.command=='show' and any(not p.get('statement') for p in found)
        return {'outcome':'incomplete' if missing else 'pass','problems':found,'total':total,
                'reason':'statement_unavailable' if missing else 'catalog_loaded',
                'catalog_provenance':data.get('provenance'), 'catalog_origin':data.get('catalog_origin'),
                'moduleDocstrings':{p['module']:data.get('moduleDocstrings',{}).get(p['module']) for p in found},
                'coverage_gaps':data.get('coverage_gaps',[]),
                'catalog_note':'Published metadata is descriptive; acceptance and exact-target verification are separate.'}
    if args.command=='status' or (args.command=='run' and args.operation=='list'):
        records=runs(root)
        for record in records:
            path=root/'.conjectures/runs'/record['id']/'publisher.json'
            if path.is_file():record['publisher']=rr.read_json(path)
        if args.command=='run':
            if args.status:records=[r for r in records if r['status']==args.status]
            records=records[:args.limit]
        from .inspection import next_action
        outstanding=[r for r in records if r['status'] not in ('completed','cancelled') or r.get('outcome') in ('fail','error','incomplete') or r.get('publisher',{}).get('status') in ('dispatching','queued','in_progress','error','cancellation_requested')]
        actions=[next_action(r) for r in outstanding]
        return {'outcome':'pass','runs':records,'outstanding':len(outstanding),'next_actions':actions,
                'next_action':None if records else 'Try conjectures review --pr 4941, or conjectures doctor --for review.'}
    if args.command=='run':
        directory=run_dir(root,args.run,readonly=args.operation!='cancel');record=rr.read_json(directory/'run.json')
        if args.operation=='show':
            from .inspection import show
            return show(root,directory,record)
        if args.operation=='logs':
            from .inspection import logs
            return logs(directory,record,args.artifact)
        if (directory/'publisher.json').is_file() and args.operation in ('wait','cancel'):
            from . import publisher
            if args.operation=='wait':return publisher.wait(directory,args.timeout)
            with run_lock(directory):return publisher.control(directory,'cancel')
        if record['kind']=='review':
            if args.operation=='cancel':
                with run_lock(directory):
                    record=rr.read_json(directory/'run.json')
                    from .review import require_pending
                    require_pending(record)
                    return finish(directory,record,'cancelled',reason='operator_cancelled',next_action='Start a new review to continue.')
            return {**record,'command_status':'incomplete' if record['status']=='awaiting_review' else 'success'}
        if importlib.util.find_spec("conjectures.proof") is None:
            raise Failure("unavailable_command","Proof controls are not included in this revision.",4)
        from .proof import control, wait
        if args.operation=='wait':return wait(directory,record,args.timeout)
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
                result=review.complete(root,directory,record,args.report or directory/'review.json',args.evidence)
                if args.post:
                    from .evidence import publish,post
                    # Publication errors never overwrite a retained semantic review outcome.
                    publication=publish(root,directory,cfg)
                    posting=post(directory,publication,cfg)
                    result={**result,'publication':publication,'publisher':posting,'command_status':posting['command_status'],'next_action':posting['next_action']}
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
                ticket=review.prepare(root,directory,pr=args.pr,repository=args.repository,collect_sources=False,semantic_review=False)
                if ticket.get('no_changed_modules'):
                    return finish(directory,record,'pass',target=ticket,reason='no_changed_modules',message='No changed Lean modules to build.')
                outcome,receipt=review.build(directory,cfg,semantic_review=False)
                return finish(directory,record,'incomplete' if outcome=='not_run' else outcome,target=ticket,receipt=receipt)
            except BaseException as error:
                finish(directory,record,'error',reason=getattr(error,'reason','execution_error'),detail=str(error));raise
        paths=[args.file] if args.file else sorted(set(git(root,'diff','--name-only',args.base).decode().splitlines()+
            [p for p in git(root,'ls-files','--others','--exclude-standard').decode().splitlines() if p.startswith('FormalConjectures/') and p.endswith('.lean')]))
        from .inspection import check_local
        return check_local(root,paths,cfg)
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
            if args.post:
                posting=post(directory,result,cfg)
                result={**result,'publisher':posting,'command_status':posting['command_status'],'next_action':posting.get('next_action')}
            return result

def operation_code(args, result):
    if result.get('command_status'):
        return {'success':0,'failure':1,'error':3,'incomplete':4,'cancelled':5}[result['command_status']]
    if args.command=='show' and result.get('outcome')=='incomplete':return 4
    if args.command in ('find','show','status','completion','setup') or (args.command=='run' and args.operation in ('list','show','logs')):
        return 0
    if args.command=='review' and args.operation=='prepare':
        build=result.get('build_status')
        if build=='fail':return 1
        if build=='error':return 3
        sources=(result.get('target') or {}).get('source_collection',{}).get('coverage')
        return 0 if build=='pass' and sources in ('available','complete') else 4
    if args.command=='verify' and result.get('status')=='queued':return 0
    if args.command=='run' and args.operation=='cancel' and result.get('status')=='cancellation_requested':return 0
    return EXIT.get(result.get('outcome'),0)


def main(argv=None):
    argv=list(sys.argv[1:] if argv is None else argv)
    if argv[:1]==['__complete']:
        from .interface import complete
        print(complete(argv[1:]));return 0
    # ArgumentParser's JSON error path also works for programmatic callers.
    original=sys.argv
    sys.argv=['conjectures',*argv]
    try:args=parse(argv)
    finally:sys.argv=original
    if args is None:return 0
    try:
        result=dispatch(args)
        if result is None:return 0
        code=operation_code(args,result)
        result={**result,'command_status':{0:'success',1:'failure',2:'failure',3:'error',4:'incomplete',5:'cancelled'}[code],'exit_code':code}
        if args.json:print(json.dumps(result,ensure_ascii=False,indent=2))
        elif 'text' in result:print(result['text'])
        else:
            from .presentation import render
            print(render(result,args))
        return code
    except (Failure,rr.InputError,OSError,ValueError,RuntimeError,subprocess.SubprocessError) as error:
        code=getattr(error,'code',3 if isinstance(error,(OSError,subprocess.SubprocessError,RuntimeError)) else 2)
        value={'command_status':'incomplete' if code==4 else 'error','outcome':'error','exit_code':code,
               'reason':getattr(error,'reason','execution_error' if code==3 else 'invalid_input'),'message':str(error)}
        if args.json:print(json.dumps(value))
        else:
            from .presentation import clean
            print(clean(value['reason']+': '+value['message']),file=sys.stderr)
        return code
    except KeyboardInterrupt:
        value={'command_status':'cancelled','outcome':'cancelled','reason':'interrupted','exit_code':5,
               'message':'Stopped waiting; remote work continues. Use run cancel RUN to cancel it.' if args.command=='run' and args.operation=='wait' else 'Operation interrupted.'}
        print(json.dumps(value) if args.json else value['message'],file=sys.stdout if args.json else sys.stderr)
        return 5

if __name__=='__main__':
    raise SystemExit(main())
