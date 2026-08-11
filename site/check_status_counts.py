#!/usr/bin/env python3
"""Check the status counts read from source against `extract_names`.

`status_counts.py` reads categories from the Lean source text so that the
stats page can show them for every commit, which a full Lean build cannot be
run for. That makes it a second implementation of rules that live in
`scripts/extract_names.lean`, and a change to the attribute syntax could make
the two disagree without anything failing.

This compares the two over the checked out tree, where both see the same
files, so any such drift fails the build instead of quietly reaching the
website. It is not meaningful in website-only mode, where the extraction comes
from the live site and the source tree does not match it.

Usage:
  lake exe extract_names ... > site/data/conjectures.json
  python3 site/check_status_counts.py site/data/conjectures.json
"""

import argparse
import json
import os
import pathlib
import sys

import status_counts

# The count each status is reported under, in report order.
LABELS = {
    'open': 'research open',
    'solved': 'research solved',
    'formal': 'formally proved',
}


class DataError(Exception):
    """Input that cannot be compared, as opposed to a disagreement."""


def count_source(root):
    """Counts the statuses over the Lean files `status_counts` looks at.

    Args:
        root (pathlib.Path): Directory the repository is checked out in

    Returns:
        dict[str, int]: Count for each of `status_counts.STATUSES`
    """
    totals = dict.fromkeys(status_counts.STATUSES, 0)
    for path in sorted(root.glob('FormalConjectures/**/*.lean')):
        relative = path.relative_to(root).as_posix()
        if not status_counts.SOURCE_PATH.match(relative):
            continue
        counted = status_counts.count_statuses(
            path.read_text(encoding='utf-8', errors='replace'))
        for status, count in counted.items():
            totals[status] += count
    return totals


def count_extraction(path):
    """Counts the statuses in the JSON `extract_names` writes.

    Args:
        path (str): Location of the extraction

    Returns:
        dict[str, int]: Count for each of `status_counts.STATUSES`
    """
    try:
        raw = json.loads(pathlib.Path(path).read_text(encoding='utf-8'))
    except OSError as error:
        raise DataError(f'cannot read {path}: {error}')
    except json.JSONDecodeError as error:
        raise DataError(f'{path} is not valid JSON: {error}')
    if not isinstance(raw, dict):
        raise DataError(f'{path} is not a JSON object')
    problems = raw.get('problems')
    if not isinstance(problems, list):
        raise DataError(f'{path} has no `problems` list')

    totals = dict.fromkeys(status_counts.STATUSES, 0)
    for index, problem in enumerate(problems):
        if not isinstance(problem, dict):
            raise DataError(f'{path}: entry {index} is not an object')
        if 'category' not in problem:
            raise DataError(f'{path}: entry {index} has no `category`')
        if problem['category'] == 'research open':
            totals['open'] += 1
        elif problem['category'] == 'research solved':
            totals['solved'] += 1
        # A formal proof is recorded independently of the category, and the
        # repository has them on `textbook` and `test` statements too.
        if problem.get('formalProofKind'):
            totals['formal'] += 1
    return totals


def summarise(lines):
    """Append to the workflow run summary, or to stdout when run by hand."""
    text = '\n'.join(lines) + '\n'
    path = os.environ.get('GITHUB_STEP_SUMMARY')
    if not path:
        print(text, end='')
        return
    with open(path, 'a', encoding='utf-8') as handle:
        handle.write(text)


def report(source, extraction):
    lines = ['### Status counts', '']
    lines.append('| Status | From source | From `extract_names` |')
    lines.append('| --- | ---: | ---: |')
    for status, label in LABELS.items():
        mark = '' if source[status] == extraction[status] else ' ⚠️'
        lines.append(
            f'| `{label}` | {source[status]} | {extraction[status]}{mark} |')
    return lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('extraction',
                        help='the JSON written by `lake exe extract_names`')
    parser.add_argument('--root', default='.',
                        help='the repository checkout to read Lean files from')
    args = parser.parse_args(argv)

    try:
        extraction = count_extraction(args.extraction)
        source = count_source(pathlib.Path(args.root))
    except DataError as error:
        print(f'::error::{error}')
        return 2

    summarise(report(source, extraction))
    for status, label in LABELS.items():
        print(f'{label}: {source[status]} from source, '
              f'{extraction[status]} from extract_names')

    differing = [s for s in status_counts.STATUSES
                 if source[s] != extraction[s]]
    if differing:
        for status in differing:
            print(f'::error file=site/status_counts.py,title=status count '
                  f'mismatch::{LABELS[status]} counted {source[status]} from '
                  f'source but {extraction[status]} by extract_names')
        print('\n`site/status_counts.py` reads categories from the Lean source '
              'so they can be counted for past commits. It no longer agrees '
              'with `extract_names`, so the plot on the stats page would '
              'disagree with the numbers on the landing page. Its rules need '
              'to follow whatever changed.')
        summarise(['', f'**Failing**: {len(differing)} status count(s) '
                       'disagree with `extract_names`.'])
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
