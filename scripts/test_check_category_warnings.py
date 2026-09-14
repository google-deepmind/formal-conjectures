#!/usr/bin/env python3
"""Tests for `check_category_warnings.py`.

Run with `python3 -m unittest discover -s scripts -p 'test_*.py'`.
No dependencies beyond the standard library.
"""

import contextlib
import io
import json
import os
import pathlib
import tempfile
import unittest
import unittest.mock

import check_category_warnings as cw


def problem(theorem, category, has_proof, module="FormalConjectures.Example"):
    return {
        "theorem": theorem,
        "module": module,
        "category": category,
        "hasSorryFreeProof": has_proof,
    }


class ClassifyTest(unittest.TestCase):

    def test_each_code(self):
        found = cw.classify([
            problem("A", "research open", True),
            problem("B", "test", False),
            problem("C", "API", False),
        ], "test")
        self.assertEqual({d[0] for d in found}, set(cw.CODES))

    def test_healthy_combinations_are_silent(self):
        found = cw.classify([
            problem("A", "research open", False),
            problem("B", "research solved", True),
            problem("C", "test", True),
            problem("D", "API", True),
            problem("E", "textbook", False),
            problem("F", "textbook", True),
        ], "test")
        self.assertEqual(found, set())

    def test_duplicate_records_collapse(self):
        found = cw.classify([problem("A", "test", False)] * 3, "test")
        self.assertEqual(len(found), 1)

    def test_same_name_in_two_modules_stays_distinct(self):
        found = cw.classify([
            problem("M_two", "test", False, "FormalConjectures.ErdosProblems.«36»"),
            problem("M_two", "test", False, "FormalConjectures.Wikipedia.Dedekind"),
        ], "test")
        self.assertEqual(len(found), 2)

    def test_unicode_names_survive(self):
        name = "Arxiv.«1609.08688».erdős_problem"
        found = cw.classify([problem(name, "test", False)], "test")
        self.assertEqual({d[1] for d in found}, {name})

    def test_missing_field(self):
        entry = problem("A", "test", False)
        del entry["hasSorryFreeProof"]
        with self.assertRaisesRegex(cw.DataError, "hasSorryFreeProof"):
            cw.classify([entry], "test")

    def test_wrong_field_type(self):
        entry = problem("A", "test", False)
        entry["hasSorryFreeProof"] = "false"
        with self.assertRaisesRegex(cw.DataError, "hasSorryFreeProof"):
            cw.classify([entry], "test")

    def test_entry_not_an_object(self):
        with self.assertRaisesRegex(cw.DataError, "not an object"):
            cw.classify(["A"], "test")


class ModulePathTest(unittest.TestCase):

    def test_plain(self):
        self.assertEqual(
            cw.module_to_path("FormalConjectures.Wikipedia.ScholzConjecture"),
            "FormalConjectures/Wikipedia/ScholzConjecture.lean")

    def test_quoted_numeral(self):
        self.assertEqual(
            cw.module_to_path("FormalConjectures.ErdosProblems.«36»"),
            "FormalConjectures/ErdosProblems/36.lean")

    def test_dot_inside_quotes_is_not_a_separator(self):
        self.assertEqual(
            cw.module_to_path("FormalConjectures.Arxiv.«1609.08688»"),
            "FormalConjectures/Arxiv/1609.08688.lean")


class MainTest(unittest.TestCase):
    """End to end, including exit codes and the run summary."""

    def setUp(self):
        self.dir = pathlib.Path(
            self.enterContext(tempfile.TemporaryDirectory()))
        self.summary = self.dir / "summary.md"
        self.enterContext(unittest.mock.patch.dict(
            os.environ, {"GITHUB_STEP_SUMMARY": str(self.summary)}))

    def extraction(self, problems):
        path = self.dir / "conjectures.json"
        path.write_text(json.dumps({"problems": problems}), encoding="utf-8")
        return str(path)

    def run_main(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cw.main(argv)
        summary = (self.summary.read_text(encoding="utf-8")
                   if self.summary.exists() else "")
        return code, out.getvalue(), summary

    def test_research_open_with_proof_fails(self):
        path = self.extraction([problem("A", "research open", True)])
        code, out, summary = self.run_main([path])
        self.assertEqual(code, 1)
        self.assertIn("::error file=FormalConjectures/Example.lean", out)
        self.assertIn("**Failing**", summary)

    def test_advisory_only_succeeds(self):
        path = self.extraction([problem("A", "test", False)])
        code, out, summary = self.run_main([path])
        self.assertEqual(code, 0)
        self.assertIn("| `test_without_proof` | 1 |", summary)
        self.assertNotIn("::error", out)

    def test_clean_input_succeeds_quietly(self):
        path = self.extraction([problem("A", "research solved", True)])
        code, out, summary = self.run_main([path])
        self.assertEqual(code, 0)
        self.assertIn("| `test_without_proof` | 0 |", summary)
        self.assertNotIn("::", out)

    def test_malformed_extraction_fails_loudly(self):
        path = self.dir / "conjectures.json"
        path.write_text("{not json", encoding="utf-8")
        code, out, _ = self.run_main([str(path)])
        self.assertEqual(code, 2)
        self.assertIn("::error::", out)

    def test_missing_file_fails_loudly(self):
        code, out, _ = self.run_main([str(self.dir / "absent.json")])
        self.assertEqual(code, 2)
        self.assertIn("::error::", out)

    def test_missing_problems_list_fails(self):
        path = self.dir / "conjectures.json"
        path.write_text(json.dumps({"moduleDocstrings": {}}), encoding="utf-8")
        code, _, _ = self.run_main([str(path)])
        self.assertEqual(code, 2)


if __name__ == "__main__":
    unittest.main()
