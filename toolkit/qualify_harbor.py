"""End-to-end Harbor qualification with digest-pinned solver and verifier images.

No model is invoked. Harbor's oracle agent writes fixed submissions and its nop agent
leaves the exported placeholder. Every trial, including unexpected outcomes, is retained.
"""
import argparse
import json
import shutil
from pathlib import Path
from conjectures import core, evaluation

# trial: (exported case, agent, submission edits, expected status, expected reward)
TRIALS = {
    'plain-unfinished': ('plain', 'nop', None, 'rejected', 0),
    'plain-imported': ('plain', 'oracle', [('sorry', 'exact PackageExportFixture.plain')], 'rejected', 0),
    'plain-valid': ('plain', 'oracle', [('sorry', 'decide')], 'verified', 1),
    'numerical-valid': ('numerical', 'oracle', [('sorry', 'exact 4'), ('sorry', 'rfl')], 'assessment_required', None),
}


def prepare(tasks, out):
    """Copy exported tasks into per-trial directories; exported tasks stay unchanged."""
    out.mkdir(parents=True)
    for trial, (case, agent, edits, _, _) in TRIALS.items():
        task = out/trial
        shutil.copytree(tasks/case, task)
        config = task/'task.toml'
        config.write_text(config.read_text().replace(f'name = "fc/{case}"', f'name = "fc-qualification/{trial}"', 1))
        if edits:
            # A qualification-only oracle. Exported tasks never contain solutions.
            script = ['#!/bin/sh', 'set -eu', 'python3 - <<\'PY\'', 'from pathlib import Path',
                      "path = Path('/app/Submission.lean'); text = path.read_text()"]
            script += [f'text = text.replace({old!r}, {new!r}, 1)' for old, new in edits]
            script += ["assert 'sorry' not in text, text", 'path.write_text(text)', 'PY', '']
            (task/'solution').mkdir()
            (task/'solution/solve.sh').write_text('\n'.join(script))
            (task/'solution/solve.sh').chmod(0o755)
    return {trial: agent for trial, (_, agent, _, _, _) in TRIALS.items()}


def check(jobs, receipt, details):
    trials = {}
    for path in sorted(jobs.rglob('result.json')):
        value = json.loads(path.read_text())
        if not isinstance(value, dict) or 'trial_name' not in value:
            continue
        name = value['task_name'].rsplit('/', 1)[-1]
        verifier = path.parent/'verifier'
        fc_path = verifier/'fc-result.json'
        fc = json.loads(fc_path.read_text()) if fc_path.is_file() else None
        reward = (value.get('verifier_result') or {}).get('rewards')
        trials[name] = {
            'trial': value['trial_name'],
            'agent': value['agent_info']['name'],
            'verifier_environment_mode': value.get('verifier_environment_mode'),
            'harbor_rewards': reward,
            'reward_file': (verifier/'reward.txt').read_text().strip() if (verifier/'reward.txt').is_file() else None,
            'harbor_exception': (value.get('exception_info') or {}).get('exception_type'),
            'fc_status': fc and fc['status'],
            'policy_outcome': fc and fc['policy_outcome'],
            'reason': fc and (fc.get('reason') or ((fc.get('verification') or {}).get('comparator') or {}).get('reason')),
            'stage': fc and ((fc.get('verification') or {}).get('comparator') or {}).get('stage'),
            'submission_artifact': [p.relative_to(path.parent).as_posix() for p in (path.parent/'artifacts').rglob('Submission.lean')],
        }
    failures = []
    for name, (_, agent, _, status, reward) in TRIALS.items():
        actual = trials.get(name)
        if actual is None:
            failures.append(f'{name}: no Harbor trial result')
            continue
        expected_reward = None if reward is None else str(reward)
        if actual['fc_status'] != status:
            failures.append(f'{name}: expected {status}, retained {actual["fc_status"]}')
        if actual['reward_file'] != expected_reward:
            failures.append(f'{name}: expected reward {expected_reward}, retained {actual["reward_file"]}')
        if actual['verifier_environment_mode'] != 'separate':
            failures.append(f'{name}: verifier did not run in a separate environment')
        if actual['agent'] != agent:
            failures.append(f'{name}: expected agent {agent}, ran {actual["agent"]}')
    summary = evaluation.summarize(jobs)
    core.save(receipt, {**details, 'model_calls': 0, 'trials': trials, 'summary': summary['counts'],
                        'failures': failures, 'conclusion': 'passed' if not failures else 'failed'})
    print(json.dumps({'trials': trials, 'summary': summary['counts'], 'failures': failures}, indent=2))
    return 1 if failures else 0


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    s = sub.add_parser('prepare'); s.add_argument('--tasks', type=Path, required=True); s.add_argument('--out', type=Path, required=True)
    s = sub.add_parser('check'); s.add_argument('--jobs', type=Path, required=True); s.add_argument('--receipt', type=Path, required=True)
    s.add_argument('--details', type=Path, required=True)
    args = p.parse_args()
    if args.command == 'prepare':
        for trial, agent in prepare(args.tasks, args.out).items():
            print(f'{trial} {agent}')
        return 0
    return check(args.jobs, args.receipt, json.loads(args.details.read_text()))


if __name__ == '__main__':
    raise SystemExit(main())
