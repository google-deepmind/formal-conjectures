"""Bundle the canonical review guidance without shipping evaluation answer keys."""
from pathlib import Path
import shutil
from setuptools import setup
from setuptools.command.build_py import build_py

class Build(build_py):
    def run(self):
        super().run()
        source = Path('.agents/skills/formal-conjectures-review')
        dest = Path(self.build_lib)/'conjectures/resources/review'
        shutil.copytree(source, dest, ignore=shutil.ignore_patterns('evals'), dirs_exist_ok=True)
        for name in ('README.md','RELEASE.md'):
            shutil.copy2(Path('toolkit')/name, dest.parent/name)
setup(cmdclass={'build_py': Build})
