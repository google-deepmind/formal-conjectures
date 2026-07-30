#!/usr/bin/env python3
"""Extract Lean comments into a plain-text corpus for spell checking.

By default, this scans the repository containing this script and writes
``docs/lean_comments.txt``.  The scanner deliberately does not try to parse
Lean; it recognizes its comment and string delimiters well enough to avoid
mistaking delimiters in string literals for comments.
"""

from __future__ import annotations

import argparse
import re
import sys
import textwrap
from pathlib import Path
from typing import Iterable


EXCLUDED_DIRECTORIES = {".git", ".lake", "build"}


def is_copyright_header(comment: str) -> bool:
    """Return whether ``comment`` is a standard Apache copyright header."""
    normalized = " ".join(comment.split()).lower()
    if "copyright" not in normalized:
        return False

    # The first spelling is used by Lean/mathlib headers.  The second is the
    # equivalent header currently used throughout this repository.
    return (
        "copyright (c)" in normalized
        and "released under apache 2.0 license" in normalized
    ) or (
        "licensed under the apache license, version 2.0" in normalized
        and "limitations under the license" in normalized
    )


def _block_open_length(source: str, index: int) -> int:
    """Return the length of a block-comment opener at ``index``."""
    if index + 2 < len(source) and source[index + 2] in "-!":
        return 3
    return 2


def _consume_block_comment(source: str, start: int) -> tuple[str, int]:
    """Consume a possibly nested block comment beginning at ``start``."""
    index = start + _block_open_length(source, start)
    depth = 1
    pieces: list[str] = []

    while index < len(source) and depth:
        if source.startswith("/-", index):
            depth += 1
            index += _block_open_length(source, index)
        elif source.startswith("-/", index):
            depth -= 1
            index += 2
        else:
            pieces.append(source[index])
            index += 1

    return "".join(pieces), index


def _consume_quoted(source: str, start: int, raw: bool) -> int:
    """Consume a normal or triple-quoted Lean string literal."""
    if source.startswith('\"\"\"', start):
        end = source.find('\"\"\"', start + 3)
        return len(source) if end == -1 else end + 3

    index = start + 1
    while index < len(source):
        if source[index] == "\\" and not raw:
            index += 2
        elif source[index] == '\"':
            return index + 1
        else:
            index += 1
    return len(source)


def _consume_char_literal(source: str, start: int) -> int | None:
    """Consume a Lean character literal, returning ``None`` when not one."""
    if start + 2 >= len(source) or source[start + 1].isspace():
        return None
    if source[start + 1] == "\\":
        index = start + 2
        while index < len(source) and source[index] != "'":
            index += 1
        return index + 1 if index < len(source) else None
    return start + 3 if source[start + 2] == "'" else None


def extract_comments(source: str) -> list[str]:
    """Extract ordinary and nested block comments from Lean source text."""
    comments: list[str] = []
    index = 0

    while index < len(source):
        if source.startswith("--", index):
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            comments.append(source[index + 2 : end])
            index = end
        elif source.startswith("/-", index):
            comment, index = _consume_block_comment(source, index)
            comments.append(comment)
        elif source[index] == '\"':
            raw = source[index - 1 : index] == "r" and (
                index < 2 or not (source[index - 2].isalnum() or source[index - 2] == "_")
            )
            index = _consume_quoted(source, index, raw)
        elif source[index] == "'":
            char_end = _consume_char_literal(source, index)
            index = char_end if char_end is not None else index + 1
        else:
            index += 1

    return comments


def _remove_backtick_code(text: str) -> str:
    """Remove matched inline/fenced backtick code, never retaining backticks."""
    result: list[str] = []
    index = 0
    while index < len(text):
        if text[index] != "`":
            result.append(text[index])
            index += 1
            continue

        run_end = index
        while run_end < len(text) and text[run_end] == "`":
            run_end += 1
        delimiter = text[index:run_end]
        close = text.find(delimiter, run_end)
        if close == -1:
            # A malformed delimiter is punctuation rather than reliably
            # identifiable code.  Removing it preserves subsequent prose.
            index = run_end
        else:
            index = close + len(delimiter)
    return "".join(result)


def clean_comment(comment: str) -> str:
    """Remove code and link destinations while retaining human-readable prose."""
    text = _remove_backtick_code(comment)
    # Markdown links and images retain their visible label.  Repeating this
    # handles the common (if unusual) case of a link label containing a link.
    link_pattern = re.compile(r"!?\[([^\]]*)\]\([^)]*\)")
    while link_pattern.search(text):
        text = link_pattern.sub(r"\1", text)
    text = re.sub(r"!?\[([^\]]+)\]\[[^\]]*\]", r"\1", text)
    text = re.sub(r"(?m)^\s*\[[^\]]+\]:\s*\S+.*$", "", text)
    text = re.sub(r"<(?:https?://|www\.)[^>\s]+>", "", text)
    text = re.sub(r"(?:https?://|www\.)[^\s)>\]}]+", "", text)
    text = text.replace("`", "")

    lines = [line.strip() for line in textwrap.dedent(text).splitlines()]
    text = "\n".join(lines)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def lean_files(root: Path) -> Iterable[Path]:
    """Yield repository Lean files in deterministic, repository-relative order."""
    paths = (
        path
        for path in root.rglob("*.lean")
        if not any(part in EXCLUDED_DIRECTORIES for part in path.relative_to(root).parts)
    )
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix())


def build_corpus(root: Path) -> str:
    """Build the complete documentation corpus for ``root``."""
    sections: list[str] = []
    for path in lean_files(root):
        relative_path = path.relative_to(root).as_posix()
        comments = extract_comments(path.read_text(encoding="utf-8"))
        prose = [clean_comment(comment) for comment in comments if not is_copyright_header(comment)]
        prose = [comment for comment in prose if comment]
        section = f"===== BEGIN FILE: {relative_path} ====="
        if prose:
            section += "\n\n" + "\n\n".join(prose)
        sections.append(section)
    return "\n\n".join(sections) + ("\n" if sections else "")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    repository_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=repository_root, help="repository root to scan")
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="corpus path (default: docs/lean_comments.txt)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the output file is missing or differs, without writing it",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    root = args.root.resolve()
    output = (args.output or root / "docs" / "lean_comments.txt").resolve()
    corpus = build_corpus(root)

    if args.check:
        if output.is_file() and output.read_text(encoding="utf-8") == corpus:
            return 0
        print(f"{output} is out of date; run {Path(__file__).as_posix()} to regenerate it.", file=sys.stderr)
        return 1

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(corpus, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
