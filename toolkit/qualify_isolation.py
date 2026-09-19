"""Real poisoned-build regression for the production runner; no model invocation."""
import argparse
import hashlib
import json
from pathlib import Path
from conjectures import execution as ex, review


def qualify(prepared, image, output):
    output.mkdir(parents=True, exist_ok=False)
    snapshot = output / 'snapshot'
    review.restore(prepared, snapshot)
    source = snapshot / 'FormalConjectures/ReviewIsolation.lean'
    prefix = '''/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil
/-! # Production build isolation fixture -/
namespace ReviewIsolation
/-- Check the frozen candidate rather than a replacement Lake target. -/
@[category test, AMS 11]
'''
    invalid = prefix + 'theorem candidate : False := by trivial\nend ReviewIsolation\n'
    valid = prefix + 'theorem candidate : True := True.intro\nend ReviewIsolation\n'
    source.write_text(invalid)
    command = ['lake', '--wfail', 'build', 'FormalConjectures.ReviewIsolation']
    results = {}

    def build(name):
        container = ex.isolated(image, snapshot)
        try:
            results[name] = ex.execute(container, command, 120)
        finally:
            ex.run('docker', 'rm', '-f', container)
        (output / (name + '.json')).write_text(json.dumps(results[name], indent=2) + '\n')
        return results[name]['exit_code']

    assert build('invalid') == 1
    scratch = ex.isolated(image, snapshot)
    try:
        results['poison'] = ex.execute(scratch, ['sh', '-c',
            "printf '%s\\n' 'name = \"probe\"' '[[lean_lib]]' "
            "'name = \"FormalConjectures.ReviewIsolation\"' 'roots = []' > lakefile.toml; "
            'lake --wfail build FormalConjectures.ReviewIsolation'])
        (output / 'poison.json').write_text(json.dumps(results['poison'], indent=2) + '\n')
        assert results['poison']['exit_code'] == 0
        assert build('after_poison') == 1
        assert source.read_text() == invalid
        source.write_text(valid)
        assert build('valid') == 0
        assert build('valid_repeat') == 0
    finally:
        ex.run('docker', 'rm', '-f', scratch)
    receipt = {'status': 'pass', 'image': image, 'cases': results,
               'runner_sha256': hashlib.sha256(Path(ex.__file__).read_bytes()).hexdigest(),
               'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (output / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS: production builds reject the candidate after scratch poisoning; valid control passes twice.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared-run', type=Path, required=True)
    parser.add_argument('--image', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    qualify(args.prepared_run, args.image, args.out)
