#!/usr/bin/env python3
"""Export every declaration in a Lean-defined subset, retaining all failures."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import sys

from export_problem import ROOT, SOURCE_REPOSITORY, export, run, source_pin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--module', default='FormalConjectures.Subsets.FC100OpenSet1')
    parser.add_argument('--declaration', default='Subsets.FC100OpenSet1.problems')
    parser.add_argument('--source-ref', default='origin/main', help='Exact source revision to qualify')
    parser.add_argument('--source-repository', default=SOURCE_REPOSITORY)
    args = parser.parse_args()
    if args.out.exists():
        parser.error('Output already exists')
    revision = source_pin(args.source_ref)
    run(['lake', '--wfail', 'build', 'export_problem', args.module])
    run(['lake', '--wfail', 'build'], cwd=args.generator)
    args.out.mkdir(parents=True)
    targets_path = args.out / "targets.json"
    run(["lake", "env", ".lake/build/bin/export_problem", "--list-set", args.module,
         args.declaration, "--output", str(targets_path)])
    targets = json.loads(targets_path.read_text())

    def check(item):
        try:
            workspace = export(ROOT / item['path'], item['declaration'],
                               args.out / item['declaration'], args.generator, revision,
                               args.source_repository, build=False)
            return dict(item, status='pass', workspace=str(workspace))
        except Exception as error:
            return dict(item, status='fail', error=str(error))

    results = []
    with ThreadPoolExecutor(max_workers=2) as pool:
        for result in pool.map(check, targets):
            results.append(result)
            print(f"{len(results)}/{len(targets)} {result['status']}: {result['declaration']}", flush=True)
            (args.out / 'report.json').write_text(json.dumps(
                {'sourceRepository': args.source_repository, 'sourceCommit': revision, 'set': args.declaration, 'results': results}, indent=2)+'\n')
    failed = sum(r['status'] != 'pass' for r in results)
    print(f'{len(results) - failed}/{len(results)} exports passed; {failed} failures')
    return bool(failed)


if __name__ == '__main__':
    sys.exit(main())
