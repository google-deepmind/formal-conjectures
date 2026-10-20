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

"""Tests for `apply_shake_imports.py`."""

import unittest

from apply_shake_imports import Suggestion, apply_to_source, classify, parse_report

REPORT = """\
./FormalConjecturesUtil.lean:
  remove #[public import FormalConjecturesForMathlib]
./FormalConjectures/ErdosProblems/1.lean:
  add #[public import FormalConjecturesForMathlib.Data.Set.Density, meta import FormalConjecturesForMathlib.Combinatorics.Basic, public import FormalConjecturesForMathlib.Combinatorics.Basic]
./FormalConjectures/ErdosProblems/2.lean:
  remove #[public meta import FormalConjecturesUtil]
  add #[meta import Mathlib.Data.ZMod.Basic]
"""

SOURCE = """\
/-
Copyright 2026 The Formal Conjectures Authors.
-/
module

public import FormalConjecturesUtil
meta import FormalConjecturesForMathlib.Combinatorics.Basic

/-!
# Problem
-/

@[expose] public section
"""


class ParseReportTest(unittest.TestCase):
    def test_blocks(self):
        suggestions = parse_report(REPORT)
        self.assertEqual([s.path for s in suggestions], [
            "FormalConjecturesUtil.lean",
            "FormalConjectures/ErdosProblems/1.lean",
            "FormalConjectures/ErdosProblems/2.lean",
        ])
        self.assertEqual(suggestions[0].removes, ["public import FormalConjecturesForMathlib"])
        self.assertEqual(len(suggestions[1].adds), 3)
        self.assertEqual(suggestions[2].adds, ["meta import Mathlib.Data.ZMod.Basic"])
        self.assertEqual(suggestions[2].removes, ["public meta import FormalConjecturesUtil"])


class ClassifyTest(unittest.TestCase):
    def test_public_sorted_and_deduplicated(self):
        suggestion = Suggestion("f", adds=[
            "public import FormalConjecturesForMathlib.B",
            "import FormalConjecturesForMathlib.A",
            "public import FormalConjecturesForMathlib.A",
        ])
        public, meta, skipped = classify(suggestion, "theorem foo : True := trivial")
        self.assertEqual(public, [
            "public import FormalConjecturesForMathlib.A",
            "public import FormalConjecturesForMathlib.B",
        ])
        self.assertEqual(meta, [])
        self.assertEqual(skipped, [])

    def test_meta_only_when_evaluating(self):
        suggestion = Suggestion("f", adds=["meta import FormalConjecturesForMathlib.A"])
        _, meta, skipped = classify(suggestion, "example : True := by native_decide")
        self.assertEqual(meta, ["meta import FormalConjecturesForMathlib.A"])
        self.assertEqual(skipped, [])
        _, meta, skipped = classify(suggestion, "example : True := trivial")
        self.assertEqual(meta, [])
        self.assertEqual(len(skipped), 1)

    def test_foreign_modules_and_removes_are_reported(self):
        suggestion = Suggestion("f", adds=["meta import Mathlib.Data.ZMod.Basic"],
                                removes=["public import FormalConjecturesUtil"])
        public, meta, skipped = classify(suggestion, "")
        self.assertEqual((public, meta), ([], []))
        self.assertEqual(len(skipped), 2)


class ApplyTest(unittest.TestCase):
    def test_insertion_points(self):
        new_source, count = apply_to_source(
            SOURCE,
            ["public import FormalConjecturesForMathlib.Data.Set.Density"],
            ["meta import FormalConjecturesForMathlib.Combinatorics.Basic",
             "meta import FormalConjecturesForMathlib.Data.Set.Density"],
        )
        self.assertEqual(count, 2)
        self.assertIn(
            "public import FormalConjecturesUtil\n"
            "public import FormalConjecturesForMathlib.Data.Set.Density\n"
            "meta import FormalConjecturesForMathlib.Combinatorics.Basic\n"
            "meta import FormalConjecturesForMathlib.Data.Set.Density\n"
            "\n/-!",
            new_source,
        )

    def test_idempotent(self):
        once, count = apply_to_source(SOURCE, ["public import FormalConjecturesForMathlib.X"], [])
        self.assertEqual(count, 1)
        twice, count = apply_to_source(once, ["public import FormalConjecturesForMathlib.X"], [])
        self.assertEqual(count, 0)
        self.assertEqual(once, twice)

    def test_requires_util_import(self):
        with self.assertRaises(ValueError):
            apply_to_source("module\n\npublic import Mathlib\n", ["public import FormalConjecturesForMathlib.X"], [])


if __name__ == "__main__":
    unittest.main()
