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

"""Tests for how `check_erdos_status.py` reads upstream statuses and closes issues."""

import contextlib
import io
import unittest

from check_erdos_status import issues_to_close, problem_status, yaml_status_to_category


def issue(number, problem, repo="solved", site="formally solved"):
    return {
        "number": number,
        "title": f"Erdős Problem {problem}: status mismatch "
                 f"(repo={repo}, erdosproblems.com={site})",
    }


def category(problem):
    """The category the script reads a YAML problem as, with any warning discarded."""
    return category_and_warning(problem)[0]


def category_and_warning(problem):
    """The category the script reads a YAML problem as, and what it wrote to stderr."""
    with contextlib.redirect_stderr(io.StringIO()) as warning:
        return yaml_status_to_category(*problem_status(problem)), warning.getvalue()


class ProblemStatusTest(unittest.TestCase):

    def test_reads_both_status_fields(self):
        self.assertEqual(
            category({"informal_status": {"state": "proved"},
                      "formal_status": {"state": "Lean"}}), "formally solved")

    def test_a_missing_formal_status_claims_no_formalisation(self):
        # A guessed formalisation attaches the `formalisation exists elsewhere` label
        # to an issue with nothing behind it.
        self.assertEqual(category({"informal_status": {"state": "proved"}}), "solved")

    def test_a_null_formal_status_block_claims_no_formalisation(self):
        # PyYAML turns `formal_status:` with no body into None, so the `or {}` guard
        # carries this case. Without it the script dies on an AttributeError.
        self.assertEqual(
            category({"informal_status": {"state": "proved"}, "formal_status": None}),
            "solved")

    def test_a_null_formal_state_claims_no_formalisation(self):
        # `state:` with no value is a present key, so a `.get` default never fires for
        # it. Read as a formalisation, it labels an issue with a proof that is not there.
        self.assertEqual(
            category({"informal_status": {"state": "proved"},
                      "formal_status": {"state": None}}), "solved")

    def test_a_missing_informal_status_warns_and_is_unreadable(self):
        # Not "open". A real status for an absent field is a positive claim: if upstream
        # ever renames this field, every problem reads as open. That reports 205 false
        # mismatches and makes every open problem's issue closable. The warning is the
        # only signal a human gets, so assert that half of warn-and-skip too.
        cat, warning = category_and_warning({"formal_status": {"state": "Lean"}})
        self.assertIsNone(cat)
        self.assertIn("unrecognized YAML informal status state", warning)

    def test_a_null_status_block_is_unreadable(self):
        # PyYAML turns `informal_status:` with no body into None, not into {}.
        self.assertIsNone(category({"informal_status": None}))


class YamlStatusToCategoryTest(unittest.TestCase):

    def test_reads_an_unsettled_problem_as_open(self):
        self.assertEqual(yaml_status_to_category("open", "unformalized"), "open")

    def test_reads_a_settled_problem_with_no_formalisation_as_solved(self):
        self.assertEqual(yaml_status_to_category("proved", "unformalized"), "solved")

    def test_a_lean_proof_makes_a_settled_problem_formally_solved(self):
        self.assertEqual(yaml_status_to_category("proved", "Lean"), "formally solved")

    def test_any_formal_state_other_than_unformalized_counts(self):
        # Upstream writes both 'Lean' and 'formalized', and CONTRIBUTING.md documents
        # only 'Lean'. A match on that spelling alone skipped Erdős 1, 74 and 126.
        self.assertEqual(
            yaml_status_to_category("disproved", "formalized"), "formally solved")

    def test_a_formalised_open_problem_is_still_open(self):
        # `scan_lean_files` calls a problem here 'formally solved' only when it is
        # solved AND carries a formal_proof, so an open problem with a Lean statement
        # of it must stay open on both sides. 26 problems in this repository are open
        # and carry a formal_proof; the other reading mismatches every one of them.
        self.assertEqual(yaml_status_to_category("open", "Lean"), "open")

    def test_the_other_open_states_are_open(self):
        self.assertEqual(
            [yaml_status_to_category(s, "unformalized")
             for s in ("falsifiable", "verifiable")],
            ["open", "open"])

    def test_decidable_is_open(self):
        # Upstream defines it as "both falsifiable and verifiable, but not yet solved".
        # Both of those are open above, so their conjunction cannot be solved. Read as
        # solved, it kept false sync issues open for Erdős 506 and 742.
        self.assertEqual(yaml_status_to_category("decidable", "unformalized"), "open")

    def test_the_set_theoretic_undecided_states_are_open(self):
        # Upstream defines both as "open in general", with a model of set theory that
        # settles the problem one way. Read as solved, they mismatch every repository
        # file that correctly says open, as they did for Erdős 1176.
        self.assertEqual(
            [yaml_status_to_category(s, "unformalized")
             for s in ("not provable", "not disprovable")],
            ["open", "open"])

    def test_independence_is_a_resolution(self):
        # The one set-theoretic state that settles a problem, so it stays solved.
        # Erdős 1119 is `research solved` in this repository and agrees.
        self.assertEqual(
            yaml_status_to_category("independent", "unformalized"), "solved")

    def test_it_reads_the_informal_state_first(self):
        # Both arguments are strings, so swapping them at a call site type-checks.
        # Reversed, nothing classifies and the script acts on nothing.
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertIsNone(yaml_status_to_category("unformalized", "open"))

    def test_an_unknown_informal_state_is_unreadable(self):
        # None, not a guess. `classifiable` turns this into "leave the issue alone".
        # The warning goes to stderr; swallow it so it does not read as a failure.
        with contextlib.redirect_stderr(io.StringIO()) as warning:
            self.assertIsNone(yaml_status_to_category("something new", "unformalized"))
        self.assertIn("something new", warning.getvalue())


class IssuesToCloseTest(unittest.TestCase):

    def test_closes_when_the_mismatch_is_gone(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open=set(), known={"71"}), [100])

    def test_keeps_one_that_still_mismatches(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open={"71"}, known={"71"}), [])

    def test_keeps_one_whose_status_cannot_be_read(self):
        # A problem missing from `known` is one the classifier returned None for.
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


if __name__ == "__main__":
    unittest.main()
