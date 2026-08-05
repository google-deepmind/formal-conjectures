#!/usr/bin/env python3
"""Surface the category warnings that `extract_names` already produces.

`scripts/extract_names.lean` notices three things: a `research open` problem
with a sorry-free proof, and `test` or `API` statements without one. It writes
them to stderr, and the workflow step that runs it ends in `|| true`, so they
land in the middle of a build log unread.

The three are not equally serious:

* A `research open` problem with a sorry-free proof is a contradiction in the
  repository and fails the build.
* A `test` or `API` statement without a proof is worth seeing but not worth
  blocking on. Adding the statement is better than not adding it, and someone
  else often supplies the proof shortly after. Those are reported, and written
  to the workflow run summary so they are visible without opening a log.

Usage:
  lake exe extract_names ... 2> warnings.txt
  python check_category_warnings.py warnings.txt
"""

import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

BLOCKING = ("research_open_with_proof",
            re.compile(r"categorised as `research open` but has a sorry-free proof"))

ADVISORY = [
    ("test_without_proof",
     re.compile(r"categorised as `test` but has no sorry-free proof")),
    ("api_without_proof",
     re.compile(r"categorised as `API` but has no sorry-free proof")),
]


def names(text, pattern):
    """Declaration names on the lines matching `pattern`."""
    out = []
    for line in text.splitlines():
        if pattern.search(line):
            m = re.search(r"Theorem (\S+)", line)
            if m:
                out.append(m.group(1))
    return sorted(out)


def summarise(lines):
    """Append to the workflow run summary, when running under Actions."""
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not path:
        return
    with open(path, "a", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def main(argv):
    if not argv:
        print("usage: check_category_warnings.py <extract_names stderr>")
        return 2

    text = pathlib.Path(argv[0]).read_text(encoding="utf-8", errors="replace")

    kind, pattern = BLOCKING
    blocking = names(text, pattern)

    advisory = [(k, names(text, p)) for k, p in ADVISORY]
    summary = ["### Category warnings", ""]
    for k, found in advisory:
        print(f"{k}: {len(found)}")
        summary.append(f"- `{k}`: {len(found)}")
    summary.append("")
    summary.append("These are advisory. A `test` or `API` statement without a proof is "
                   "still better than no statement, and the proof often follows later.")
    summarise(summary)

    if blocking:
        print(f"\n{kind}: {len(blocking)}")
        for n in blocking:
            print(f"  {n}")
        print("\nA problem categorised as `research open` should not have a sorry-free "
              "proof. Either the proof settles it, in which case the category should be "
              "`research solved`, or the proof is of something weaker than the statement.")
        summarise(["", f"**Failing**: {len(blocking)} `research open` "
                       "problem(s) with a sorry-free proof."])
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
