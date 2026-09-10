"""Argument parsing, help, and shell discovery. No repository or network access."""
import argparse
import json
import sys
from pathlib import Path
from . import __version__

DOCS = 'https://github.com/williamjblair/formal-conjectures/blob/codex/fc-toolkit-integration/toolkit/README.md'


class ArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        if '--json' in sys.argv:
            print(json.dumps({'command_status':'failure','outcome':'error','reason':'invalid_arguments','message':message,'exit_code':2}))
            raise SystemExit(2)
        super().error(message)


def positive(value):
    number = int(value)
    if number <= 0: raise argparse.ArgumentTypeError('Use a positive integer.')
    return number


def parser():
    p = ArgumentParser(prog='conjectures', description='Browse FC problems, review contributions in your existing session, and retain evidence.',
        epilog='Start: conjectures doctor\nTry: conjectures find erdos/730\nReview: conjectures review --pr 4941\nGuide: '+DOCS,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--version', action='version', version=__version__)
    p.add_argument('--json', action='store_true', help='Return structured output for agents and scripts')
    p.add_argument('--repo', type=Path, help='FC checkout to use (default: current checkout)')
    sub = p.add_subparsers(dest='command', required=True)
    def command(name, help, example=None, parent=sub):
        q=parent.add_parser(name,help=help,description=help,epilog=('Example: '+example+'\n' if example else '')+'Guide: '+DOCS,
                            formatter_class=argparse.RawDescriptionHelpFormatter)
        q.add_argument('--json',action='store_true',default=argparse.SUPPRESS,help='Structured output')
        return q
    q=command('skill','Locate or explicitly install bundled agent guidance','conjectures skill install --dir .agents/skills')
    r=q.add_subparsers(dest='operation',required=True)
    for op in ('path','install'):
        s=command(op,'Print bundled guidance location' if op=='path' else 'Copy guidance into an explicit skills directory',parent=r)
        s.add_argument('--name',choices=['conjectures','formal-conjectures-review'],default='conjectures')
        if op=='install':s.add_argument('--dir',type=Path,required=True,help='Parent skill discovery directory, e.g. .agents/skills or .claude/skills')
    q=command('doctor','Check readiness without changing configuration','conjectures doctor --for review')
    q.add_argument('--for',dest='capability',choices=['browse','review','verify','evidence'],help='Return readiness for this capability')
    for name in ('find','show'):
        q=command(name,'Search the catalog' if name=='find' else 'Read a statement, its variants, sources, and evidence',f'conjectures {name} erdos/730')
        q.add_argument('target',help='Search text, exact declaration, or erdos/NUMBER')
        q.add_argument('--catalog',type=Path,help='Read a native FC metadata JSON file')
        freshness=q.add_mutually_exclusive_group()
        freshness.add_argument('--refresh',action='store_true',help='Refresh the published catalog now (otherwise cached for 24 hours)')
        freshness.add_argument('--offline',action='store_true',help='Use the retained catalog without network requests')
        if name=='find':q.add_argument('--limit',type=positive,default=20,help='Maximum results (default: 20)')
    def scope(q, replay=False):
        g=q.add_mutually_exclusive_group(required=True)
        g.add_argument('--changed',action='store_true',help='Use local changes against --base')
        g.add_argument('--pr',type=positive,help='Public GitHub PR number')
        if replay:g.add_argument('--input',type=Path,help='Replay a retained preparation directory')
        else:g.add_argument('file',nargs='?',help='Lean problem file to build')
        q.add_argument('--base',default='origin/main',help='Local comparison ref (default: origin/main)')
        q.add_argument('--repository',help='GitHub OWNER/REPO (default: checkout origin)')
    q=command('check','Build the selected problem modules','conjectures check --changed');scope(q)
    q=command('review','Prepare a review for your existing agent, then validate its findings','conjectures review --pr 4941')
    r=q.add_subparsers(dest='operation',required=True)
    s=command('prepare','Freeze sources and isolated checks; semantic review remains pending','conjectures review prepare --pr 4941',r)
    scope(s,True);s.add_argument('--sources',type=Path,help='Directory of supplied source documents')
    s=command('finish','Validate and retain the externally written review','conjectures review finish RUN',r)
    s.add_argument('run',help='Run ID or unique prefix');s.add_argument('--report',type=Path,help='Review JSON (default: this run’s review.json)')
    s.add_argument('--evidence',type=Path,help='Directory of additional operator evidence')
    s.add_argument('--post',action='store_true',help='Explicitly archive, then post an advisory PR summary')
    s=command('exec','Run a bounded witness in a fresh isolated container','conjectures review exec RUN -- lake env lean scratch/Witness.lean',r)
    s.add_argument('run');s.add_argument('--files',type=Path,help='Directory containing witness files; copied to scratch/')
    q=command('init','Generate a workspace for one exact declaration (experimental)','conjectures init DECLARATION --out ../proof')
    q.add_argument('target');q.add_argument('--out',required=True,type=Path,help='New workspace directory')
    q.add_argument('--source-ref',help='Retrievable source revision (default: catalog commit; required for unversioned local catalogs)')
    q.add_argument('--repository',help='Source GitHub OWNER/REPO');q.add_argument('--catalog',type=Path,help='Native metadata JSON')
    q=command('verify','Verify a proof workspace with the configured Linux executor (experimental)','conjectures verify ../proof');q.add_argument('directory',type=Path)
    command('status','Show work, coverage, outcomes, and next actions','conjectures status')
    q=command('run','Inspect saved work or control remote verification','conjectures run show latest');r=q.add_subparsers(dest='operation',required=True)
    for op in ('list','show','logs','wait','cancel'):
        s=command(op,{'list':'List local records','show':'Inspect one record','logs':'Read retained log contents','wait':'Wait for a remote result; Ctrl-C leaves remote work running','cancel':'Request cancellation of one explicit run'}[op],f'conjectures run {op}'+('' if op=='list' else ' RUN'),r)
        if op!='list':s.add_argument('run',help='Run ID or unique prefix'+(' (or latest)' if op!='cancel' else ''))
        if op=='list':
            s.add_argument('--limit',type=positive,default=20,help='Maximum records (default: 20)');s.add_argument('--status',help='Filter by recorded status, e.g. awaiting_review')
        if op=='logs':s.add_argument('--artifact',help='Relative artifact path to display')
        if op=='wait':s.add_argument('--timeout',type=positive,default=600,help='Maximum wait in seconds (default: 600)')
    q=command('evidence','Inspect and explicitly publish evidence (experimental)','conjectures evidence publish RUN --dry-run');r=q.add_subparsers(dest='operation',required=True)
    s=command('publish','Archive a validated public export','conjectures evidence publish RUN --dry-run',r)
    s.add_argument('run');s.add_argument('--post',action='store_true',help='Post a fresh advisory PR summary after archiving')
    s.add_argument('--dry-run',action='store_true',help='Inspect the local public export without publishing')
    q=command('setup','Configure one capability explicitly','conjectures setup review');r=q.add_subparsers(dest='operation',required=True)
    for op in ('review','verify','evidence'):
        s=command(op,{'review':'Build or select a pinned review image','verify':'Configure an existing qualified Linux executor','evidence':'Configure an existing public evidence branch'}[op],parent=r)
        s.add_argument('--global',dest='global_config',action='store_true',help='Save in user configuration instead of this checkout')
        if op=='review':
            s.add_argument('--image',help='Existing image pinned by SHA-256 digest')
            s.add_argument('--source-ref',default='main',help='Reviewed upstream main revision used to build the image')
        else:
            s.add_argument('--repository',required=True,help='Existing GitHub OWNER/REPO')
            s.add_argument('--ref' if op=='verify' else '--branch',required=True,help='Qualified exact executor commit' if op=='verify' else 'Existing data-only branch')
    q=command('completion','Print shell completion for installation','conjectures completion zsh');q.add_argument('shell',choices=['bash','zsh','fish'])
    return p


def subparser(p, name):
    for action in p._actions:
        if isinstance(action,argparse._SubParsersAction): return action.choices.get(name)


def parse(argv):
    argv=list(argv)
    # Only FC flags before the command separator are normalized. Witness argv is opaque.
    tail=[]
    if '--' in argv:
        i=argv.index('--');tail=argv[i+1:];argv=argv[:i]
    globals=[];rest=[];i=0
    while i<len(argv):
        token=argv[i]
        if token=='--json':globals.append(token)
        elif token=='--repo':
            globals.append(token)
            if i+1<len(argv):i+=1;globals.append(argv[i])
        elif token.startswith('--repo='):globals.append(token)
        else:rest.append(token)
        i+=1
    p=parser()
    if rest[:1]==['help']:rest=rest[1:]+['--help']
    if rest[:1]==['review'] and len(rest)>1 and rest[1] not in ('prepare','finish','exec','--help','-h'):
        rest.insert(1,'prepare')
    if not rest:p.print_help();return None
    if rest in (['review'],['run'],['setup'],['evidence']):subparser(p,rest[0]).print_help();return None
    if rest==['--version'] and '--json' in globals:
        print(json.dumps({'version':__version__,'command_status':'success','exit_code':0}));return None
    args=p.parse_args(globals+rest)
    if tail and not (args.command=='review' and args.operation=='exec'):p.error('Only review exec accepts a command after --')
    if args.command=='review' and args.operation=='exec':
        if not tail:p.error('Use review exec RUN -- COMMAND')
        args.arguments=tail
    return args


def complete(words):
    p=parser();prefix=words[-1] if words else ''; tokens=words[:-1]
    for token in tokens:
        child=subparser(p,token)
        if child:p=child
    options=[o for a in p._actions for o in a.option_strings]
    choices=[name for a in p._actions if isinstance(a,argparse._SubParsersAction) for name in a.choices]
    return '\n'.join(x for x in choices+options if x.startswith(prefix))


def completion(shell):
    if shell == 'bash':
        return """_conjectures() { local IFS=$'\\n'; COMPREPLY=( $(conjectures __complete "${COMP_WORDS[@]:1}") ); }
complete -F _conjectures conjectures"""
    if shell == 'zsh':
        return """#compdef conjectures
_conjectures() { local -a choices; choices=("${(@f)$(conjectures __complete "${words[@]:1}")}"); _describe 'conjectures' choices; }
compdef _conjectures conjectures"""
    return "complete -c conjectures -f -a '(conjectures __complete (commandline -opc | tail -n +2) (commandline -ct))'"
