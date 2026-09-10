"""Build the pinned proof tools for an operator-owned Linux executor."""
import subprocess
import sys
from pathlib import Path
from .core import Failure, command, git
from .proof import PINS


def build(toolkit,tools):
    toolkit=toolkit.resolve();tools=tools.resolve();tools.mkdir(parents=True,exist_ok=True)
    if sys.platform!='linux':raise Failure('unqualified_executor','Build verifier tools on Linux.',4)
    for name,(repository,revision) in PINS.items():
        path=tools/name
        if not path.exists():
            git(tools,'init',path)
            git(path,'fetch','--depth','1','https://github.com/'+repository+'.git',revision)
            git(path,'checkout','--detach',revision)
        if git(path,'rev-parse','HEAD').decode().strip()!=revision or git(path,'status','--porcelain','--untracked-files=no').strip():
            raise Failure('tool_pin_mismatch',f'{path} differs from its required revision. Existing files were preserved.',4)
        print('Building pinned '+name+'…',file=sys.stderr)
        args=['go','build','-o','landrun','./cmd/landrun'] if name=='landrun' else ['cargo','build','--release'] if name=='nanoda' else ['lake','--wfail','build']
        subprocess.run(args,cwd=path,stdout=sys.stderr,stderr=sys.stderr,check=True,timeout=1800)
    print('Building the toolchain-compatible Lean exporter…',file=sys.stderr)
    subprocess.run(['lake','-d',str(toolkit/'comparator/verifier'),'build','lean4export/lean4export'],
                   stdout=sys.stderr,stderr=sys.stderr,check=True,timeout=1800)
