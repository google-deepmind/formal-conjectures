"""Exercise the actual workflow mode script against changes in a Git checkout."""
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

WORKFLOW = Path(__file__).resolve().parents[1] / '.github/workflows/build-and-docs.yml'


class SiteBuildModeTests(unittest.TestCase):
    def test_shared_inputs_build_the_site_but_problem_only_changes_do_not(self):
        step = WORKFLOW.read_text().split('      - name: Detect build mode\n', 1)[1].split('\n      - name:', 1)[0]
        script = textwrap.dedent(step.split('        run: |\n', 1)[1])
        with tempfile.TemporaryDirectory(prefix='fc-build-mode-') as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-C', directory, *args], stderr=subprocess.DEVNULL).decode().strip()
            git('init'); git('config', 'user.name', 'Fixture'); git('config', 'user.email', 'fixture@example.invalid')
            git('commit', '--allow-empty', '-m', 'Base')
            for changed, expected in [
                ('FormalConjecturesUtil/ProblemMetadata.lean', 'true'),
                ('FormalConjecturesUtil/Metadata.lean', 'true'),
                ('FormalConjecturesUtil.lean', 'true'),
                ('FormalConjecturesUtil/Answer.lean', 'true'),
                ('toolkit/conjectures/metadata.py', 'true'),
                ('toolkit/conjectures/catalog_data.py', 'true'),
                ('toolkit/conjectures/resources/schemas/catalog-v2.schema.json', 'true'),
                ('scripts/extract_names.lean', 'true'),
                ('lake-manifest.json', 'true'), ('lean-toolchain', 'true'),
                ('lakefile.toml', 'true'), ('docbuild/lakefile.toml', 'true'),
                ('FormalConjectures/Example.lean', 'false'),
            ]:
                with self.subTest(changed=changed):
                    file = root / changed
                    file.parent.mkdir(parents=True, exist_ok=True); file.write_text('fixture\n')
                    git('add', changed); git('commit', '-m', changed)
                    output = root / 'output'; output.write_text('')
                    env = dict(os.environ, EVENT_NAME='pull_request', WEBSITE_ONLY='false',
                               REF_NAME='fixture', GITHUB_OUTPUT=str(output))
                    subprocess.run(['bash', '-eu', '-c', script], cwd=root, env=env,
                                   capture_output=True, text=True, check=True)
                    self.assertIn('site='+expected, output.read_text().splitlines())
