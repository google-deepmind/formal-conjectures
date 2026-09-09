#!/usr/bin/env python3
"""Opt-in Actions preparation using the shared, model-free toolkit."""
import argparse
import os
from pathlib import Path
import review_report as rr
from conjectures import core, review


def authorize(event, permission):
    rr.require(event.get('action')=='created' and event['comment']['body']=='/review',
               'expected an exact /review comment')
    rr.require('pull_request' in event['issue'], 'review requires a pull request')
    rr.require(permission in ('admin','maintain','write'), 'review requires write permission')


def prepare(root):
    event = rr.read_json(Path(os.environ['GITHUB_EVENT_PATH']))
    repo = os.environ['GITHUB_REPOSITORY']
    permission = core.github(f"repos/{repo}/collaborators/{event['comment']['user']['login']}/permission")
    authorize(event,permission['permission'])
    pr = core.github(f"repos/{repo}/pulls/{event['issue']['number']}")
    rr.require(pr['state']=='open','PR is closed')
    directory, record = core.start_run(root,'review')
    try:
        record['producer']='github_actions'
        ticket=review.prepare(Path.cwd(),directory,pr=event['issue']['number'],repository=repo)
        record['target']=ticket
        cfg=core.config(root)
        cfg['image']=os.environ.get('REVIEW_IMAGE') or None
        result=review.handoff(directory,cfg,record)
    except BaseException as error:
        core.finish(directory,record,'error',reason=getattr(error,'reason','execution_error'),detail=str(error))
        raise
    # Preparation has no model output and no publication rights. A contributor replays
    # these inputs locally through review prepare --input before supplying their review.
    print(rr.encode(result).decode())
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('prepare',))
    parser.add_argument('--root',type=Path,required=True)
    args=parser.parse_args()
    args.root.mkdir(parents=True,exist_ok=True)
    prepare(args.root.resolve())
