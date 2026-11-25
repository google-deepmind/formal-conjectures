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
from unittest import mock

from check_erdos_status import (
    FORMALISED_LABEL,
    SYNC_LABEL,
    issues_to_close,
    label_changes,
    plan_issue_sync,
    problem_status,
    sync_issues,
    yaml_status_to_category,
)


def issue(number, problem, repo="solved", site="formally solved", labels=None):
    """A sync issue. Its labels default to the ones the script gives for `site`."""
    if labels is None:
        labels = [SYNC_LABEL] + ([FORMALISED_LABEL] if site == "formally solved" else [])
    return {
        "number": number,
        "title": f"Erdős Problem {problem}: status mismatch "
                 f"(repo={repo}, erdosproblems.com={site})",
        "labels": [{"name": label} for label in labels],
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


def mismatch(problem, repo="solved", site="formally solved"):
    return {"number": problem, "lean_status": repo, "yaml_status": site}


class PlanIssueSyncTest(unittest.TestCase):

    def test_creates_an_issue_for_a_new_mismatch(self):
        m = mismatch("71")
        self.assertEqual(plan_issue_sync([m], []), ([m], [], []))

    def test_an_open_issue_with_the_current_title_needs_nothing(self):
        self.assertEqual(plan_issue_sync([mismatch("71")], [issue(100, "71")]), ([], [], []))

    def test_does_not_match_a_problem_by_prefix(self):
        # "Erdős Problem 4" is a prefix of "Erdős Problem 43". The issue for 43 must not
        # count as an issue for 4.
        m = mismatch("4")
        self.assertEqual(plan_issue_sync([m], [issue(100, "43")]), ([m], [], []))

    def test_retitles_an_issue_whose_sides_changed(self):
        # Erdős 848: the issue says erdosproblems.com=solved, but the script now reads open.
        m = mismatch("848", repo="formally solved", site="open")
        old = issue(4053, "848", repo="formally solved", site="solved")
        self.assertEqual(plan_issue_sync([m], [old]), ([], [(old, m)], []))

    def test_closes_newer_duplicates_and_keeps_the_oldest(self):
        # Erdős 43 had #5119 and #7544 open together.
        m = mismatch("43")
        issues = [issue(7544, "43"), issue(5119, "43")]
        self.assertEqual(plan_issue_sync([m], issues), ([], [], [(7544, 5119)]))

    def test_retitles_only_the_kept_issue_of_a_duplicate_pair(self):
        m = mismatch("43", site="open")
        issues = [issue(5119, "43"), issue(7544, "43")]
        self.assertEqual(
            plan_issue_sync([m], issues), ([], [(issues[0], m)], [(7544, 5119)]))

    def test_edits_an_issue_with_a_current_title_and_a_stale_label(self):
        m = mismatch("71", site="open")
        old = issue(100, "71", site="open", labels=[SYNC_LABEL, FORMALISED_LABEL])
        self.assertEqual(plan_issue_sync([m], [old]), ([], [(old, m)], []))

    def test_edits_an_issue_with_a_current_title_and_a_missing_label(self):
        m = mismatch("71")
        old = issue(100, "71", labels=[SYNC_LABEL])
        self.assertEqual(plan_issue_sync([m], [old]), ([], [(old, m)], []))

    def test_unmanaged_labels_need_no_edit(self):
        old = issue(100, "71", site="open", labels=[SYNC_LABEL, "erdos-problems"])
        self.assertEqual(plan_issue_sync([mismatch("71", site="open")], [old]), ([], [], []))

    def test_leaves_issues_for_resolved_problems_to_issues_to_close(self):
        self.assertEqual(
            plan_issue_sync([], [issue(5119, "43"), issue(7544, "43")]), ([], [], []))

    def test_ignores_issues_with_an_unrelated_title(self):
        m = mismatch("71")
        self.assertEqual(
            plan_issue_sync([m], [{"number": 100, "title": "Something else entirely"}]),
            ([m], [], []))


class LabelChangesTest(unittest.TestCase):

    def test_adds_the_formalised_label_on_an_upgrade(self):
        self.assertEqual(
            label_changes(mismatch("71"), issue(100, "71", site="open")),
            ([FORMALISED_LABEL], []))

    def test_removes_the_formalised_label_on_a_downgrade(self):
        for site in ("open", "solved"):
            with self.subTest(site=site):
                self.assertEqual(
                    label_changes(mismatch("71", site=site), issue(100, "71")),
                    ([], [FORMALISED_LABEL]))

    def test_keeps_unmanaged_labels(self):
        old = issue(
            100, "71", labels=[SYNC_LABEL, FORMALISED_LABEL, "erdos-problems"])
        self.assertEqual(
            label_changes(mismatch("71", site="open"), old), ([], [FORMALISED_LABEL]))


class SyncIssuesTest(unittest.TestCase):

    def commands(self, m, old, returncode=0):
        """The `gh` commands that `sync_issues` runs, without running them."""
        with mock.patch("check_erdos_status.subprocess.run") as run:
            run.return_value.returncode = returncode
            with contextlib.redirect_stderr(io.StringIO()):
                sync_issues([m], [old])
        return [call.args[0] for call in run.call_args_list]

    def test_a_downgrade_retitles_removes_the_label_and_comments(self):
        for site in ("open", "solved"):
            with self.subTest(site=site):
                edit, comment = self.commands(mismatch("71", site=site), issue(100, "71"))
                self.assertEqual(edit, [
                    "gh", "issue", "edit", "100",
                    "--title", issue(100, "71", site=site)["title"],
                    "--remove-label", FORMALISED_LABEL,
                ])
                self.assertEqual(comment[:4], ["gh", "issue", "comment", "100"])

    def test_an_upgrade_retitles_adds_the_label_and_comments(self):
        edit, comment = self.commands(mismatch("71"), issue(100, "71", site="open"))
        self.assertEqual(edit, [
            "gh", "issue", "edit", "100",
            "--title", issue(100, "71")["title"],
            "--add-label", FORMALISED_LABEL,
        ])
        self.assertEqual(comment[:4], ["gh", "issue", "comment", "100"])

    def test_a_label_correction_alone_posts_no_comment(self):
        old = issue(100, "71", site="open", labels=[SYNC_LABEL, FORMALISED_LABEL])
        self.assertEqual(
            self.commands(mismatch("71", site="open"), old),
            [["gh", "issue", "edit", "100", "--remove-label", FORMALISED_LABEL]])

    def test_a_failed_edit_posts_no_comment(self):
        commands = self.commands(mismatch("71", site="open"), issue(100, "71"), returncode=1)
        self.assertEqual([c[:3] for c in commands], [["gh", "issue", "edit"]])


if __name__ == "__main__":
    unittest.main()
