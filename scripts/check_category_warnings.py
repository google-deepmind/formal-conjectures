#!/usr/bin/env python3
"""Stop the `extract_names` category warnings from growing.

`scripts/extract_names.lean` already notices when a `research open` problem has
a sorry-free proof, or a `test` or `API` statement has none. It writes those to
stderr, and the workflow step that runs it ends in `|| true`, so the warnings
land in the middle of a build log and nobody sees them.

Fixing every existing case is not a small job (see #4747), so this does the
next best thing: it records the declarations currently warning and fails when a
new one appears. That lets the backlog be worked down at whatever pace suits
while stopping new cases from arriving unnoticed, and a failure names only what
was added rather than reprinting the whole backlog.

Usage:
  lake exe extract_names ... 2> warnings.txt
  python check_category_warnings.py warnings.txt      # check against baseline
  python check_category_warnings.py warnings.txt -u   # rewrite the baseline
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "category_warnings_baseline.json"

# The three category/sorry combinations `extract_names` reports. Docstring
# warnings are deliberately not counted here: they are a different concern and
# noisy enough to deserve their own decision.
KINDS = {
    "research_open_with_proof": re.compile(
        r"categorised as `research open` but has a sorry-free proof"),
    "test_without_proof": re.compile(
        r"categorised as `test` but has no sorry-free proof"),
    "api_without_proof": re.compile(
        r"categorised as `API` but has no sorry-free proof"),
}


def tally(text):
    """Map each kind to the sorted declaration names warning under it."""
    found = {k: set() for k in KINDS}
    for line in text.splitlines():
        m = re.search(r"Theorem (\S+)", line)
        if not m:
            continue
        for kind, pat in KINDS.items():
            if pat.search(line):
                found[kind].add(m.group(1))
    return {k: sorted(v) for k, v in found.items()}


def main(argv):
    update = "-u" in argv or "--update" in argv
    paths = [a for a in argv if not a.startswith("-")]
    if not paths:
        print("usage: check_category_warnings.py <extract_names stderr> [-u]")
        return 2

    text = pathlib.Path(paths[0]).read_text(encoding="utf-8", errors="replace")
    counts = tally(text)

    if update:
        BASELINE.write_text(json.dumps(counts, indent=2, sort_keys=True) + "\n")
        print(f"baseline written to {BASELINE.relative_to(ROOT)}:")
        for k, v in sorted(counts.items()):
            print(f"  {k}: {len(v)}")
        return 0

    if not BASELINE.is_file():
        print(f"no baseline at {BASELINE.relative_to(ROOT)}; run with -u to create one")
        return 2

    base = json.loads(BASELINE.read_text())
    added, fixed = {}, {}
    for kind in KINDS:
        now, was = set(counts[kind]), set(base.get(kind, []))
        if now - was:
            added[kind] = sorted(now - was)
        if was - now:
            fixed[kind] = sorted(was - now)

    print("category warnings against baseline:")
    for kind in sorted(KINDS):
        print(f"  {kind}: {len(counts[kind])} (baseline {len(base.get(kind, []))})")

    if fixed:
        n = sum(len(v) for v in fixed.values())
        print(f"\n{n} of the recorded cases are gone. Refresh the baseline so the gain is held:")
        print("  lake exe extract_names --exclude=statement,docstring,moduleDocstrings "
              "> /dev/null 2> warnings.txt")
        print("  python3 scripts/check_category_warnings.py warnings.txt -u")

    if added:
        print()
        for kind, decls in sorted(added.items()):
            print(f"new under {kind}:")
            for d in decls:
                print(f"  {d}")
        print("\nA `test` or `API` statement is meant to be proved, and a `research open` "
              "one is not meant to have a proof. If a category is wrong, fix the category; "
              "if the proof is missing, that is what the statement is asking for.")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
