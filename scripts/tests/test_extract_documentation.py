"""Tests for the Lean documentation extractor."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from scripts.extract_documentation import build_corpus, extract_comments, main


class ExtractCommentsTests(unittest.TestCase):
    def test_all_comment_forms_and_nested_comments(self) -> None:
        source = """-- ordinary
/- block -/
/-- doc -/
/-! module -/
/- outer /- inner -/ after -/
"""
        self.assertEqual(
            extract_comments(source),
            [" ordinary", " block ", " doc ", " module ", " outer  inner  after "],
        )

    def test_markers_in_strings_are_not_comments(self) -> None:
        source = r'''def first := "-- not a comment /- either -/"
def second := """/- also not a comment -/"""
def third := '-'
def raw := r"ends at \\" -- raw comment
-- actual
'''
        self.assertEqual(extract_comments(source), [" raw comment", " actual"])


class CorpusTests(unittest.TestCase):
    def write_lean(self, root: Path, name: str, source: str) -> None:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_cleanup_removes_code_links_urls_and_copyright_headers(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write_lean(
                root,
                "comments.lean",
                """/-
Copyright (c) 2020 Example.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-- [Visible label](https://example.com/path) and https://example.org/plain.

Use `inlineCode` here.
```lean
def hidden := true
```
Malformed ` marker leaves prose.
-/
""",
            )
            corpus = build_corpus(root)
            self.assertIn("Visible label and", corpus)
            self.assertIn("Malformed  marker leaves prose.", corpus)
            self.assertNotIn("Copyright", corpus)
            self.assertNotIn("https://", corpus)
            self.assertNotIn("inlineCode", corpus)
            self.assertNotIn("hidden", corpus)
            self.assertNotIn("`", corpus)

    def test_sorted_banners_include_files_without_comments(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write_lean(root, "z.lean", "-- last\n")
            self.write_lean(root, "a/no_comments.lean", "def x := 1\n")
            self.write_lean(root, "a/first.lean", "-- first\n")
            corpus = build_corpus(root)
            self.assertLess(corpus.index("a/first.lean"), corpus.index("a/no_comments.lean"))
            self.assertLess(corpus.index("a/no_comments.lean"), corpus.index("z.lean"))
            self.assertIn("BEGIN FILE: a/no_comments.lean", corpus)

    def test_check_does_not_write_and_detects_stale_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            output = root / "docs" / "lean_comments.txt"
            self.write_lean(root, "example.lean", "-- prose\n")
            arguments = ["--root", str(root), "--output", str(output)]
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                self.assertEqual(main(arguments + ["--check"]), 1)
            self.assertFalse(output.exists())
            self.assertEqual(main(arguments), 0)
            self.assertEqual(main(arguments + ["--check"]), 0)
            output.write_text("stale\n", encoding="utf-8")
            with contextlib.redirect_stderr(stderr):
                self.assertEqual(main(arguments + ["--check"]), 1)
            self.assertEqual(output.read_text(encoding="utf-8"), "stale\n")


if __name__ == "__main__":
    unittest.main()
