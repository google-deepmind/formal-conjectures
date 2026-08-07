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

"""Tests for which sync issues `check_erdos_status.py` decides to close."""

import unittest

from check_erdos_status import (
    CATEGORY_THEN_THEOREM,
    issues_to_close,
    yaml_status_to_category,
)


def issue(number, problem, repo="solved", site="formally solved"):
    return {
        "number": number,
        "title": f"Erdős Problem {problem}: status mismatch "
                 f"(repo={repo}, erdosproblems.com={site})",
    }


class IssuesToCloseTest(unittest.TestCase):

    def test_closes_when_the_mismatch_is_gone(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open=set(), known={"71"}), [100])

    def test_keeps_one_that_still_mismatches(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open={"71"}, known={"71"}), [])

    def test_keeps_one_whose_status_cannot_be_read(self):
        # A problem missing from `known` has a YAML state the script does not recognise.
        # That is "we cannot tell", which must not be read as "resolved".
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open=set(), known=set()), [])

    def test_compares_problem_numbers_as_strings(self):
        # `find_mismatches` keys problems by string; comparing an int against that set
        # silently matches nothing and would close everything.
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open={"71"}, known={"71"}), [])

    def test_ignores_issues_with_an_unrelated_title(self):
        self.assertEqual(
            issues_to_close([{"number": 100, "title": "Something else entirely"}],
                            still_open=set(), known={"71"}), [])

    def test_handles_several_at_once(self):
        issues = [issue(1, "71"), issue(2, "209"), issue(3, "353")]
        self.assertEqual(
            issues_to_close(issues, still_open={"209"}, known={"71", "209"}), [1])


class CategoryScanTest(unittest.TestCase):

    def test_reads_an_attribute_on_one_line(self):
        src = "@[category research open, AMS 11]\ntheorem erdos_42 : True := by sorry\n"
        self.assertEqual([m.groups() for m in CATEGORY_THEN_THEOREM.finditer(src)],
                         [("open", "42", "")])

    def test_reads_an_attribute_wrapped_over_two_lines(self):
        # 25 problem files wrap theirs, usually to fit a `formal_proof` URL, and were
        # invisible to this scanner while the pattern used `.*`.
        src = ('@[category research solved, AMS 5, formal_proof using lean4 at\n'
               '  "https://example.com/x.lean"]\n'
               'theorem erdos_183 : True := by sorry\n')
        self.assertEqual([m.groups() for m in CATEGORY_THEN_THEOREM.finditer(src)],
                         [("solved", "183", "")])

    def test_does_not_run_past_its_own_attribute(self):
        src = ("@[category research open]\ntheorem erdos_1 : True := by sorry\n\n"
               "@[category research solved]\ntheorem erdos_2 : True := by sorry\n")
        self.assertEqual([m.group(2) for m in CATEGORY_THEN_THEOREM.finditer(src)],
                         ["1", "2"])

    def test_keeps_the_variant_suffix(self):
        src = "@[category research solved]\ntheorem erdos_42.variants.foo : True := by sorry\n"
        self.assertEqual([m.groups() for m in CATEGORY_THEN_THEOREM.finditer(src)],
                         [("solved", "42", ".variants.foo")])


class YamlStatusTest(unittest.TestCase):

    def test_open_with_a_lean_statement_is_still_open(self):
        self.assertEqual(yaml_status_to_category("open (Lean)"), "open")

    def test_solved_in_lean_is_formally_solved(self):
        self.assertEqual(yaml_status_to_category("solved (Lean)"), "formally solved")

    def test_plain_solved_is_solved(self):
        self.assertEqual(yaml_status_to_category("proved"), "solved")

    def test_unknown_state_is_none(self):
        self.assertIsNone(yaml_status_to_category("something new"))


if __name__ == "__main__":
    unittest.main()
