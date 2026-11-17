#!/usr/bin/env python3
"""Check Palomar Lean source and submission requirements locally before building or submitting.

Default mode checks repository-wide Lean source rules that apply even on the base
`palomar_prepare` branch:
  - Every regular `.lean` file (except `lakefile.lean`) begins with the `module` keyword.
  - Every `.lean` file has at most 10,000 physical lines.
  - No `.lean` symbolic links or committed build artifacts (`.olean`, `.ilean`, etc.) exist.
  - If `Challenge.lean` exists, checks its stricter size caps (<= 1,000 lines, <= 100 KiB)
    and verifies that it does not directly import `FormalConjecturesUtil` or
    `FormalConjecturesForMathlib` (Palomar requires `Challenge.lean`'s transitive import
    closure to resolve strictly to Lean core / Mathlib / Tau Ceti / CSLib).

Pass `--submission` when validating a completed Palomar submission to also require:
  - `Challenge.lean`, `Solution.lean`, `comparator.json`, and `formalization.yaml` exist.
  - `comparator.json` has the required schema and permitted axioms.
  - `formalization.yaml` has no remaining `TEMPLATE` placeholder values.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")

FORBIDDEN_ARTIFACT_SUFFIXES = {
    ".olean",
    ".ilean",
    ".a",
    ".bc",
    ".dll",
    ".dylib",
    ".o",
    ".obj",
    ".so",
    ".trace",
}

PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
ALLOWED_COMPARATOR_KEYS = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "definition_names",
    "permitted_axioms",
    "enable_nanoda",
}
FORBIDDEN_CHALLENGE_IMPORT = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(FormalConjectures\w*(?:\.\S*)?)",
    re.MULTILINE,
)


def has_module_header(text: str) -> bool:
    """Recognize the initial `module` keyword after plain whitespace/comments."""
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    """Count LF/CRLF lines; an unterminated final line counts, a trailing LF adds none."""
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def check_repo_tree(root: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name
            for name in subdirectories
            if name not in {".git", ".lake", ".cache", "__pycache__"}
            and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            relative = path.relative_to(root)
            suffix = path.suffix.lower()

            if suffix in FORBIDDEN_ARTIFACT_SUFFIXES:
                errors.append(
                    f"{relative}: compiled build artifact outside .lake is rejected by Palomar"
                )
                continue

            if not name.endswith(".lean"):
                continue

            if path.is_symlink():
                errors.append(f"{relative}: must be a regular Lean file, not a symbolic link")
                continue

            if not path.is_file():
                continue

            raw = path.read_bytes()
            try:
                text = raw.decode("utf-8")
            except UnicodeDecodeError:
                errors.append(f"{relative}: source is not valid UTF-8")
                continue

            if path.name != "lakefile.lean" and not has_module_header(text):
                errors.append(f"{relative}: must start with the `module` header keyword")

            lines = physical_lines(text)
            if lines > 10_000:
                errors.append(f"{relative}: {lines} lines exceeds Palomar's 10,000-line limit")

            if relative == Path("Challenge.lean"):
                size_bytes = len(raw)
                if lines > 1_000:
                    errors.append(
                        f"Challenge.lean: {lines} lines exceeds Palomar's 1,000-line Challenge limit"
                    )
                elif lines > 300:
                    warnings.append(
                        f"Challenge.lean: {lines} lines exceeds Palomar's 300-line auditability warning threshold"
                    )
                if size_bytes > 100 * 1024:
                    errors.append(
                        f"Challenge.lean: {size_bytes} bytes exceeds Palomar's 100 KiB Challenge limit"
                    )
                elif size_bytes > 32 * 1024:
                    warnings.append(
                        f"Challenge.lean: {size_bytes} bytes exceeds Palomar's 32 KiB auditability warning threshold"
                    )
                for match in FORBIDDEN_CHALLENGE_IMPORT.finditer(text):
                    errors.append(
                        f"Challenge.lean: imports `{match.group(1)}`, which Palomar rejects in Challenge's "
                        "transitive import closure (Challenge may import only Lean core / Mathlib; inline "
                        "any needed definitions into Challenge.lean and keep FormalConjectures* imports in Solution.lean)"
                    )

    return errors, warnings


def check_submission_files(root: Path) -> list[str]:
    errors: list[str] = []

    for required in ("Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml", "LICENSE"):
        if not (root / required).is_file():
            errors.append(f"{required}: missing required Palomar submission file")

    comp_path = root / "comparator.json"
    if comp_path.is_file():
        try:
            comp = json.loads(comp_path.read_text(encoding="utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            errors.append(f"comparator.json: invalid JSON ({exc})")
        else:
            if not isinstance(comp, dict):
                errors.append("comparator.json: top-level JSON value must be an object")
            else:
                unknown = set(comp.keys()) - ALLOWED_COMPARATOR_KEYS
                if unknown:
                    errors.append(
                        f"comparator.json: unsupported keys {sorted(unknown)} "
                        "(note: `external_kernels` must not appear in submitted comparator.json)"
                    )
                for key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
                    if key not in comp:
                        errors.append(f"comparator.json: missing required key `{key}`")
                theorems = comp.get("theorem_names")
                if not isinstance(theorems, list) or not theorems or not all(
                    isinstance(t, str) and t.strip() for t in theorems
                ):
                    errors.append("comparator.json: `theorem_names` must be a nonempty list of strings")
                axioms = comp.get("permitted_axioms")
                if not isinstance(axioms, list) or not set(axioms).issubset(PERMITTED_AXIOMS):
                    errors.append(
                        f"comparator.json: `permitted_axioms` may contain only {sorted(PERMITTED_AXIOMS)}"
                    )

    yaml_path = root / "formalization.yaml"
    if yaml_path.is_file():
        yaml_text = yaml_path.read_text(encoding="utf-8")
        for lineno, line in enumerate(yaml_text.splitlines(), 1):
            stripped = line.lstrip()
            if stripped.startswith("#"):
                continue
            if "TEMPLATE:" in line or re.search(r'["\']TEMPLATE["\']', line):
                errors.append(
                    f"formalization.yaml:{lineno}: contains unreplaced TEMPLATE placeholder: {line.strip()}"
                )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--submission",
        action="store_true",
        help="Require Challenge.lean, Solution.lean, comparator.json, and a filled-in formalization.yaml",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    errors, warnings = check_repo_tree(root)
    if args.submission:
        errors.extend(check_submission_files(root))

    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    for error in errors:
        print(f"error: {error}", file=sys.stderr)

    if errors:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
