"""Discover and install portable guidance without changing agent configuration."""
import shutil
import tempfile
from pathlib import Path
from .core import Failure


def path(name='conjectures'):
    if name == 'formal-conjectures-review':
        from .review import skill_path
        return skill_path()
    packaged = Path(__file__).parent/'resources/agent-skill'
    source = Path(__file__).resolve().parents[2]/'.agents/skills/conjectures'
    result = packaged if packaged.is_dir() else source
    if not (result/'SKILL.md').is_file():
        raise Failure('skill_unavailable', 'Reinstall the toolkit: bundled guidance is missing.', 4)
    return result


def install(name, directory):
    """--dir names the parent discovery directory, never an agent config file."""
    source = path(name)
    parent = directory.expanduser().resolve()
    parent.mkdir(parents=True, exist_ok=True)
    target = parent/name
    files = {p.relative_to(source).as_posix():p.read_bytes() for p in source.rglob('*')
             if p.is_file() and not p.is_symlink() and 'evals' not in p.relative_to(source).parts}
    if target.exists() or target.is_symlink():
        existing = {p.relative_to(target).as_posix():p.read_bytes() for p in target.rglob('*')
                    if p.is_file() and not p.is_symlink()}
        if target.is_symlink() or any(p.is_symlink() for p in target.rglob('*')) or existing != files:
            raise Failure('skill_exists', f'{target} contains different guidance. Choose another --dir; existing files were preserved.')
    else:
        with tempfile.TemporaryDirectory(prefix='.conjectures-skill-', dir=parent) as temp:
            staging = Path(temp)/name
            for name_, raw in files.items():
                p = staging/name_;p.parent.mkdir(parents=True, exist_ok=True);p.write_bytes(raw)
            staging.rename(target)
    return {'outcome':'pass', 'paths':{'skill':str(target/'SKILL.md')},
            'message':'Skill installed. Reload your agent to discover it; no agent configuration was changed.'}
