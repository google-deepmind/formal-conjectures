#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Apply the import suggestions of `scripts/shake_imports.lean` to problem files.

Usage:

    python3 scripts/apply_shake_imports.py REPORT [--dry-run]

`REPORT` is the standard output of `scripts/shake_imports.lean`. Only `add` suggestions of
`FormalConjecturesForMathlib.*` modules for files below `FormalConjectures/` are applied, always as
`public import`. A `meta import` is applied only when the file evaluates code (`native_decide`,
`decide +native`, `decide +kernel` or `#eval`); other `meta` suggestions record compiler inlining
and are not needed to build. Every other suggestion, and every `remove`, is printed for review.

New `public import` lines go directly after `public import FormalConjecturesUtil`, new `meta import`
lines after the last import of the header. Lines already present are skipped, so the script can
be run again on a partially converted tree.
"""

import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ALLOWED_PREFIX = "FormalConjecturesForMathlib."
PROBLEM_DIR = "FormalConjectures"
UTIL_IMPORT = "public import FormalConjecturesUtil"
IMPORT_RE = re.compile(r"^(?:(public) )?(?:(meta) )?import (?:all )?(\S+)$")
EVAL_RE = re.compile(r"native_decide|\+native|\+kernel|#eval")


@dataclass
class Suggestion:
    """`shake` output for one file."""

    path: str
    adds: list[str] = field(default_factory=list)
    removes: list[str] = field(default_factory=list)


def parse_report(text: str) -> list[Suggestion]:
    """Parse the `path:` / `  add #[...]` / `  remove #[...]` blocks of a shake report."""
    suggestions: list[Suggestion] = []
    current = None
    for line in text.splitlines():
        stripped = line.strip()
        if line.startswith("  ") and stripped.startswith(("add #[", "remove #[")):
            if current is None:
                continue
            kind, _, rest = stripped.partition(" #[")
            items = [item.strip() for item in rest.rstrip("]").split(",") if item.strip()]
            (current.adds if kind == "add" else current.removes).extend(items)
        elif line.endswith(":") and not line.startswith((" ", "\t")):
            current = Suggestion(path=line[:-1])
            if current.path.startswith("./"):
                current.path = current.path[2:]
            suggestions.append(current)
    return suggestions


def classify(suggestion: Suggestion, source: str) -> tuple[list[str], list[str], list[str]]:
    """Split the adds of a suggestion into (public lines, meta lines, skipped notes)."""
    public_lines: list[str] = []
    meta_lines: list[str] = []
    skipped: list[str] = []
    evaluates = EVAL_RE.search(source) is not None
    for item in suggestion.adds:
        match = IMPORT_RE.match(item)
        if match is None:
            skipped.append(f"unrecognized suggestion `{item}`")
            continue
        public, meta, module = match.groups()
        if not module.startswith(ALLOWED_PREFIX):
            skipped.append(f"not a FormalConjecturesForMathlib module: `{item}`")
            continue
        if meta:
            if evaluates:
                meta_lines.append(f"{'public ' if public else ''}meta import {module}")
            else:
                skipped.append(f"file evaluates nothing: `{item}`")
            continue
        public_lines.append(f"public import {module}")
    for item in suggestion.removes:
        skipped.append(f"remove not applied: `{item}`")
    return sorted(set(public_lines)), sorted(set(meta_lines)), skipped


def header_bounds(lines: list[str]) -> tuple[int, int]:
    """Return (index of the `public import FormalConjecturesUtil` line, index after the last import)."""
    util_index = None
    last_import = None
    for index, line in enumerate(lines):
        if IMPORT_RE.match(line.strip()):
            last_import = index
            if line.strip() == UTIL_IMPORT:
                util_index = index
        elif line.strip() and not line.strip().startswith("module") and last_import is not None:
            break
    if util_index is None or last_import is None:
        raise ValueError(f"no `{UTIL_IMPORT}` line found")
    return util_index, last_import + 1


def apply_to_source(source: str, public_lines: list[str], meta_lines: list[str]) -> tuple[str, int]:
    """Insert the new import lines; return the new source and the number of lines added."""
    lines = source.split("\n")
    util_index, header_end = header_bounds(lines)
    existing = {line.strip() for line in lines[:header_end]}
    new_public = [line for line in public_lines if line not in existing]
    new_meta = [line for line in meta_lines if line not in existing]
    lines[header_end:header_end] = new_meta
    lines[util_index + 1 : util_index + 1] = new_public
    return "\n".join(lines), len(new_public) + len(new_meta)


def main(argv: list[str]) -> int:
    if not argv or len(argv) > 2 or (len(argv) == 2 and argv[1] != "--dry-run"):
        print(__doc__, file=sys.stderr)
        return 2
    report = Path(argv[0]).read_text(encoding="utf-8")
    dry_run = len(argv) == 2
    changed_files = 0
    added_lines = 0
    for suggestion in parse_report(report):
        path = Path(suggestion.path)
        if path.parts[:1] != (PROBLEM_DIR,):
            if suggestion.adds or suggestion.removes:
                print(f"{path}: outside {PROBLEM_DIR}/, not applied: {suggestion.adds + suggestion.removes}")
            continue
        source = path.read_text(encoding="utf-8")
        public_lines, meta_lines, skipped = classify(suggestion, source)
        for note in skipped:
            print(f"{path}: {note}")
        if not public_lines and not meta_lines:
            continue
        new_source, count = apply_to_source(source, public_lines, meta_lines)
        if count == 0:
            continue
        changed_files += 1
        added_lines += count
        if not dry_run:
            path.write_text(new_source, encoding="utf-8")
    print(f"{'would add' if dry_run else 'added'} {added_lines} import lines in {changed_files} files")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
