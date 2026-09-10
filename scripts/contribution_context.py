#!/usr/bin/env python3
"""Build the site's optional contribution projection through the installed/shared reader."""
import os
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'toolkit'))
from conjectures import report as rr
from conjectures.catalog import read_url
from conjectures.core import save
from conjectures.evidence_reader import load
from conjectures.projections import contribution_context, work_context


def main():
    repo=os.environ.get('FC_EVIDENCE_REPOSITORY');branch=os.environ.get('FC_EVIDENCE_BRANCH')
    if bool(repo)!=bool(branch):raise ValueError('Configure both evidence repository and branch')
    work=None;work_status={'status':'not_configured','pull_requests':[]};url=os.environ.get('FC_WORK_CONTEXT_URL')
    if url:
        try:
            if not url.startswith('https://'):raise ValueError('Work context must use HTTPS')
            work=work_context(rr.parse(read_url(url,8*1024*1024)))
        except (OSError,ValueError,KeyError,TypeError) as error:
            work_status={'status':'unavailable' if isinstance(error,OSError) else 'invalid','pull_requests':[],'message':str(error)}
    save(Path('site/data/work.json'),work or work_status)
    index=load(destination={'repository':repo,'branch':branch} if repo else None)
    save(Path('site/data/evidence.json'),contribution_context(index,work))


if __name__=='__main__':main()
