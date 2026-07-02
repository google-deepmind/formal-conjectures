#!/usr/bin/env python3
"""Convert a single lean-eval problem file into the formal-conjectures repo style.

Usage:
    python3 convert_lean_eval.py <source_file> <dest_file>

Transformations:
  1. Replace all `import Mathlib...` and `import EvalTools...` lines with a single
     `import FormalConjectures.Util.ProblemImports`
  2. Rewrite internal `import LeanEval.X.Y` to `import FormalConjectures.LeanEval.X.Y`
  3. Replace `@[eval_problem]` attributes with `@[category research solved, AMS 0]`
  4. Remove `#guard_msgs in` blocks (the docstring above, the #guard_msgs line,
     and the following declaration up to the next blank line)
"""

import re
import sys
from pathlib import Path


def remove_guard_msgs_blocks(lines: list[str]) -> list[str]:
    """Remove #guard_msgs in blocks along with their preceding docstrings."""
    result: list[str] = []
    i = 0
    while i < len(lines):
        # Look ahead: is there a #guard_msgs in line coming up?
        stripped = lines[i].strip()

        if stripped == '#guard_msgs in':
            # Remove the docstring block that precedes this line.
            # Walk backward through result to find and remove /-- ... -/ block
            while result and result[-1].strip() != '':
                last = result[-1].strip()
                result.pop()
                if last.startswith('/--'):
                    break
            # Also remove trailing blank lines
            while result and result[-1].strip() == '':
                result.pop()

            # Skip the #guard_msgs in line itself
            i += 1
            # Skip the following declaration block (until blank line or end)
            while i < len(lines) and lines[i].strip() != '':
                i += 1
            # Skip the trailing blank line
            if i < len(lines) and lines[i].strip() == '':
                i += 1
            continue

        result.append(lines[i])
        i += 1

    return result


def convert_file(source: Path, dest: Path) -> None:
    text = source.read_text()
    lines = text.splitlines()

    # --- Phase 1: Remove #guard_msgs blocks ---
    lines = remove_guard_msgs_blocks(lines)

    # --- Phase 2: Process imports ---
    new_lines: list[str] = []
    added_problem_imports = False

    for line in lines:
        stripped = line.strip()

        # Replace Mathlib / EvalTools imports
        if stripped.startswith('import Mathlib') or stripped.startswith('import EvalTools'):
            if not added_problem_imports:
                new_lines.append('import FormalConjectures.Util.ProblemImports')
                added_problem_imports = True
            # Skip additional Mathlib/EvalTools import lines
            continue

        # Rewrite internal LeanEval imports
        if stripped.startswith('import LeanEval.'):
            new_line = line.replace('import LeanEval.', 'import FormalConjectures.LeanEval.')
            new_lines.append(new_line)
            # We still need ProblemImports for Mathlib access
            if not added_problem_imports:
                new_lines.insert(0, 'import FormalConjectures.Util.ProblemImports')
                added_problem_imports = True
            continue

        new_lines.append(line)

    # --- Phase 3: Replace @[eval_problem] with category attribute ---
    final_lines: list[str] = []
    in_docstring = False
    in_block_comment = False
    for line in new_lines:
        stripped = line.strip()
        # Track whether we're inside a docstring or block comment
        if '/-' in stripped:
            in_block_comment = True
        if '-/' in stripped:
            in_block_comment = False
            final_lines.append(line)
            continue
        # Don't modify lines inside comments/docstrings
        if in_block_comment or stripped.startswith('--'):
            final_lines.append(line)
            continue
        # Standalone @[eval_problem]
        if stripped == '@[eval_problem]':
            final_lines.append('@[category research solved, AMS 0]')
            continue
        # Within a combined attribute list like @[eval_problem, other_attr]
        # Replace eval_problem with category research solved, AMS 0
        line = re.sub(r'eval_problem', 'category research solved, AMS 0', line)
        final_lines.append(line)

    # --- Phase 4: Clean up multiple consecutive blank lines ---
    cleaned: list[str] = []
    prev_blank = False
    for line in final_lines:
        is_blank = line.strip() == ''
        if is_blank and prev_blank:
            continue
        cleaned.append(line)
        prev_blank = is_blank

    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text('\n'.join(cleaned) + '\n' if cleaned else '')


def main() -> None:
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <source_file> <dest_file>", file=sys.stderr)
        sys.exit(1)

    source = Path(sys.argv[1])
    dest = Path(sys.argv[2])

    if not source.exists():
        print(f"Error: source file {source} does not exist", file=sys.stderr)
        sys.exit(1)

    convert_file(source, dest)
    print(f"Converted: {source} -> {dest}")


if __name__ == '__main__':
    main()
