"""Terminal presentation only. Domain results and retained outcomes stay independent."""
from contextlib import contextmanager
from contextvars import ContextVar
import os
import sys
import time


_current = ContextVar('conjectures_ui', default=None)


def console(args, *, stderr=False):
    from rich.console import Console
    stream=sys.stderr if stderr else sys.stdout
    mode=getattr(args,'color','auto')
    color=mode!='never' and 'NO_COLOR' not in os.environ
    return Console(file=stream, force_terminal=True if mode=='always' and color else None,
                   no_color=not color, color_system='auto' if color else None, highlight=False, markup=False)


class Session:
    def __init__(self,args):
        self.args=args
        self.console=console(args,stderr=True)
        self.label=None
        self.started=None
        self.live=None

    def end_stage(self, status='finished'):
        from rich.text import Text
        if self.live:
            self.live.stop();self.live=None
        if self.label:
            elapsed=time.monotonic()-self.started
            self.console.print(Text(f'{status.capitalize()}: {self.label}  ({elapsed:.1f}s)',
                                    style='dim' if status=='finished' else 'yellow'))
            self.label=None

    def stage(self,label):
        from rich.text import Text
        from rich.progress import Progress, SpinnerColumn, TextColumn, TimeElapsedColumn
        from .presentation import clean
        if getattr(self.args,'quiet',False):return
        self.end_stage()
        self.label=clean(label);self.started=time.monotonic()
        # CI, pipes and JSON callers get append-only diagnostics, never animation.
        if self.console.is_terminal and not getattr(self.args,'json',False):
            self.live=Progress(SpinnerColumn(),TextColumn('{task.description}',markup=False),
                               TimeElapsedColumn(),console=self.console,transient=True)
            self.live.add_task(self.label,total=None)
            self.live.start()
        else:self.console.print(Text('Working: '+self.label))


@contextmanager
def session(args):
    current=Session(args);token=_current.set(current)
    try:
        yield current
    except BaseException:
        current.end_stage('stopped')
        raise
    else:current.end_stage()
    finally:_current.reset(token)


def stage(message):
    current=_current.get()
    if current:current.stage(message)
    else:
        from .presentation import clean
        print(clean(message),file=sys.stderr)


def diagnostic(message):
    # Workers invoking domain operations directly need no terminal dependencies.
    current=_current.get()
    if current and getattr(current.args,'verbose',False) and not getattr(current.args,'quiet',False):
        from .presentation import clean
        from rich.text import Text
        current.console.print(Text('Detail: '+clean(message),style='dim'))


def log_location(path):
    current=_current.get()
    if current and not getattr(current.args,'quiet',False):
        from .presentation import clean
        from rich.text import Text
        current.console.print(Text('Logs: '+clean(path),style='dim'))


def output(value,args):
    from rich.text import Text
    from .presentation import render, rich_view
    out=console(args)
    # One renderer, with readable plain output retained for scripts and snapshots.
    view=rich_view(value,args) if out.is_terminal else Text(render(value,args))
    if getattr(args,'pager',False) and out.is_terminal and sys.stdin.isatty():
        # Rich's pager disables styles by default, so NO_COLOR and redirected output agree.
        with out.pager():out.print(view)
    else:out.print(view,soft_wrap=not out.is_terminal)


def error(value,args):
    from rich.text import Text
    from .presentation import clean
    out=console(args,stderr=True)
    out.print(Text('Unable to complete: ',style='bold red')+Text(clean(value['message'])))
    if getattr(args,'verbose',False):out.print(Text('Reason: '+clean(value['reason']),style='dim'))
