#!/usr/bin/env python3
"""Report the category diagnostics that `extract_names` metadata implies.

`scripts/extract_names.lean` notices three things: a `research open` problem
with a sorry-free proof, and `test` or `API` statements without one. It writes
them to stderr as prose, but every field it decides them from is already in
`site/data/conjectures.json`, so this script classifies the JSON directly
rather than parsing warning text.

The three are not equally serious:

* A `research open` problem with a sorry-free proof is a contradiction in the
  repository and fails the build.
* A `test` or `API` statement without a proof is worth seeing but not worth
  blocking on. Adding the statement is better than not adding it, and someone
  else often supplies the proof shortly after. Those counts go to the workflow
  run summary so they are visible without opening a log.

Usage:
  lake exe extract_names ... > site/data/conjectures.json
  python3 check_category_warnings.py site/data/conjectures.json
"""

import argparse
import json
import os
import pathlib
import sys

BLOCKING = "research_open_with_proof"

# In report order, with the sentence `extract_names` uses for each.
CODES = {
    "research_open_with_proof":
        "is categorised as `research open` but has a sorry-free proof",
    "test_without_proof":
        "is categorised as `test` but has no sorry-free proof",
    "api_without_proof":
        "is categorised as `API` but has no sorry-free proof",
}

REQUIRED_FIELDS = (
    ("theorem", str),
    ("module", str),
    ("category", str),
    ("hasSorryFreeProof", bool),
)


class DataError(Exception):
    """Input that cannot be classified, as opposed to a diagnostic finding."""


def diagnostic_for(problem):
    """The diagnostic code a problem earns, or `None`."""
    category = problem["category"]
    has_proof = problem["hasSorryFreeProof"]
    if category == "research open" and has_proof:
        return "research_open_with_proof"
    if category == "test" and not has_proof:
        return "test_without_proof"
    if category == "API" and not has_proof:
        return "api_without_proof"
    return None


def split_module(module):
    """The components of a Lean module name, with any `«...»` quoting removed.

    Splitting on `.` alone is wrong: `FormalConjectures.Arxiv.«1609.08688»`
    has three components, not four.
    """
    parts = []
    current = []
    depth = 0
    for ch in module:
        if ch == "«":
            depth += 1
        elif ch == "»":
            depth -= 1
        elif ch == "." and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(ch)
    parts.append("".join(current))
    return parts


def module_to_path(module):
    """The source file a module name came from, for workflow annotations."""
    return "/".join(split_module(module)) + ".lean"


def classify(problems, source):
    """The set of `(code, theorem, module)` triples the problems imply."""
    found = set()
    for index, problem in enumerate(problems):
        if not isinstance(problem, dict):
            raise DataError(f"{source}: entry {index} is not an object")
        for field, kind in REQUIRED_FIELDS:
            if field not in problem:
                raise DataError(f"{source}: entry {index} has no `{field}`")
            if not isinstance(problem[field], kind):
                raise DataError(
                    f"{source}: entry {index} has a `{field}` that is not "
                    f"{kind.__name__}")
        code = diagnostic_for(problem)
        if code:
            found.add((code, problem["theorem"], problem["module"]))
    return found


def load_extraction(path):
    """Classify the `extract_names` output at `path`."""
    try:
        text = pathlib.Path(path).read_text(encoding="utf-8")
    except OSError as error:
        raise DataError(f"cannot read {path}: {error}")
    try:
        raw = json.loads(text)
    except json.JSONDecodeError as error:
        raise DataError(f"{path} is not valid JSON: {error}")
    if not isinstance(raw, dict):
        raise DataError(f"{path} is not a JSON object")
    problems = raw.get("problems")
    if not isinstance(problems, list):
        raise DataError(f"{path} has no `problems` list")
    return classify(problems, path)


def annotate(level, code, theorem, module):
    """A workflow annotation, which GitHub attaches to the file it names."""
    print(f"::{level} file={module_to_path(module)},title={code}::"
          f"{theorem} {CODES[code]}")


def summarise(lines):
    """Append to the workflow run summary, or to stdout when run by hand."""
    text = "\n".join(lines) + "\n"
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not path:
        print(text, end="")
        return
    with open(path, "a", encoding="utf-8") as handle:
        handle.write(text)


def report(found):
    lines = ["### Category diagnostics", ""]
    lines.append("| Diagnostic | Total |")
    lines.append("| --- | ---: |")
    for code in CODES:
        total = sum(1 for d in found if d[0] == code)
        lines.append(f"| `{code}` | {total} |")
    lines.append("")
    lines.append("The advisory two are not failures. A `test` or `API` "
                 "statement without a proof is still better than no "
                 "statement, and the proof often follows later.")
    return lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("extraction",
                        help="the JSON written by `lake exe extract_names`")
    args = parser.parse_args(argv)

    try:
        found = load_extraction(args.extraction)
    except DataError as error:
        print(f"::error::{error}")
        return 2

    summarise(report(found))
    for code in CODES:
        print(f"{code}: {sum(1 for d in found if d[0] == code)}")

    blocking = sorted(d for d in found if d[0] == BLOCKING)
    for code, theorem, module in blocking:
        annotate("error", code, theorem, module)
    if blocking:
        print("\nA problem categorised as `research open` should not have a "
              "sorry-free proof. Either the proof settles it, in which case "
              "the category should be `research solved`, or the proof is of "
              "something weaker than the statement.")
        for _, theorem, _ in blocking:
            print(f"  {theorem}")
        summarise(["", f"**Failing**: {len(blocking)} `research open` "
                       "problem(s) with a sorry-free proof."])
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
