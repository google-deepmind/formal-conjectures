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
    issues_to_close,
    problem_argument,
    problem_statuses,
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


class YamlStatusTest(unittest.TestCase):

    def test_open_with_a_lean_statement_is_still_open(self):
        self.assertEqual(yaml_status_to_category("open (Lean)"), "open")

    def test_solved_in_lean_is_formally_solved(self):
        self.assertEqual(yaml_status_to_category("solved (Lean)"), "formally solved")

    def test_unknown_state_is_none(self):
        self.assertIsNone(yaml_status_to_category("something new"))


def row(num, theorem, category="research open", formal=False, conditions=None):
    out = {
        "module": f"FormalConjectures.ErdosProblems.«{num}»",
        "theorem": theorem,
        "category": category,
    }
    if formal:
        out["formalProofKind"] = "lean4"
        out["formalProofLink"] = "https://example.com/proof"
    if conditions:
        out["proofConditions"] = conditions
    return out


class ProblemStatusesTest(unittest.TestCase):

    def statuses(self, *rows):
        return problem_statuses({"conjectures": list(rows)})

    def test_open_statement_is_open(self):
        self.assertEqual(self.statuses(row("42", "Erdos42.erdos_42")), {"42": "open"})

    def test_solved_without_a_link_is_solved(self):
        self.assertEqual(
            self.statuses(row("42", "Erdos42.erdos_42", "research solved")),
            {"42": "solved"})

    def test_solved_with_a_link_is_formally_solved(self):
        self.assertEqual(
            self.statuses(row("42", "Erdos42.erdos_42", "research solved", formal=True)),
            {"42": "formally solved"})

    def test_a_link_on_a_variant_does_not_upgrade_the_problem(self):
        # A proof of `variants.x` proves the variant. Calling the problem
        # formally solved for it would report something nobody established.
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42", "research solved"),
                row("42", "Erdos42.erdos_42.variants.x", "research solved", formal=True)),
            {"42": "solved"})

    def test_one_open_part_makes_the_problem_open(self):
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.parts.i", "research solved"),
                row("42", "Erdos42.parts.ii", "research open")),
            {"42": "open"})

    def test_variants_do_not_decide_the_status(self):
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42", "research solved"),
                row("42", "Erdos42.erdos_42.variants.x", "research open")),
            {"42": "solved"})

    def test_variants_do_not_stand_in_for_a_missing_main_statement(self):
        # Erdős 92 states both its questions as variants and has no bare
        # `erdos_92`. Guessing a status from the variants was wrong on 1104;
        # silence was how 92 sat unnoticed. The state is reported as itself,
        # so the mismatch checker still surfaces the problem.
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42.variants.weak", "research open"),
                row("42", "Erdos42.erdos_42.variants.strong", "research open")),
            {"42": "no primary statement"})

    def test_a_variants_only_problem_reports_its_real_state(self):
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42.variants.weak", "research solved"),
                row("42", "Erdos42.erdos_42.variants.strong", "research solved")),
            {"42": "no primary statement"})

    def test_test_and_api_statements_are_ignored(self):
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42", "research solved"),
                row("42", "Erdos42.M_one", "test"),
                row("42", "Erdos42.helper", "API")),
            {"42": "solved"})

    def test_a_conditional_proof_does_not_settle_the_problem(self):
        # The proof establishes the statement only under hypotheses its author has not
        # proved, so the problem is solved but not formally solved.
        self.assertEqual(
            self.statuses(
                row("427", "Erdos427.erdos_427", "research solved", formal=True,
                    conditions=["Erdos427.erdos_427.variants.shiu"])),
            {"427": "solved"})

    def test_a_conditional_proof_on_the_main_statement_does_not_count(self):
        # The main statement's own proof is conditional; the variant's
        # unconditional proof proves the variant. Neither settles the problem.
        self.assertEqual(
            self.statuses(
                row("42", "Erdos42.erdos_42", "research solved", formal=True,
                    conditions=["Erdos42.hypothesis"]),
                row("42", "Erdos42.erdos_42.variants.x", "research solved", formal=True)),
            {"42": "solved"})

    def test_schema_two_proof_list_is_read(self):
        # The `formalProofs` list carries conditions per proof; one
        # unconditional entry on the main statement settles it.
        r = row("42", "Erdos42.erdos_42", "research solved")
        r["formalProofs"] = [
            {"kind": "lean4", "link": "x", "conditions": ["h"]},
            {"kind": "lean4", "link": "y", "conditions": []},
        ]
        self.assertEqual(self.statuses(r), {"42": "formally solved"})

    def test_an_in_repo_proof_counts_despite_its_empty_link(self):
        # A `formal_conjectures` proof lives in this repository and is written with an empty
        # link, so a check on the link rather than the kind would drop it. 316 and 399 are
        # written this way.
        in_repo = {
            "module": "FormalConjectures.ErdosProblems.«316»",
            "theorem": "Erdos316.erdos_316",
            "category": "research solved",
            "formalProofKind": "formal_conjectures",
            "formalProofLink": "",
        }
        self.assertEqual(problem_statuses({"conjectures": [in_repo]}),
                         {"316": "formally solved"})

    def test_a_problem_with_no_research_statement_has_no_status(self):
        self.assertEqual(self.statuses(row("42", "Erdos42.M_one", "test")), {})

    def test_other_collections_are_left_alone(self):
        other = {"module": "FormalConjectures.Wikipedia.Foo", "theorem": "Foo.bar",
                 "category": "research open", "hasFormalProof": False}
        self.assertEqual(problem_statuses({"conjectures": [other]}), {})

    def test_a_number_shared_with_another_collection_does_not_leak(self):
        # `Green36` and `Erdos36` both exist; only the module path distinguishes them.
        green = {"module": "FormalConjectures.GreensOpenProblems.«36»",
                 "theorem": "Green36.green_36", "category": "research open",
                 "hasFormalProof": False}
        self.assertEqual(
            problem_statuses({"conjectures": [green, row("36", "Erdos36.erdos_36",
                                                         "research solved")]}),
            {"36": "solved"})


if __name__ == "__main__":
    unittest.main()


class ProblemArgumentTest(unittest.TestCase):

    def test_reads_the_number_after_the_flag(self):
        self.assertEqual(problem_argument(["prog", "--problem", "80"]), "80")

    def test_absent_flag_gives_none(self):
        self.assertIsNone(problem_argument(["prog"]))

    def test_absent_flag_with_other_arguments_gives_none(self):
        self.assertIsNone(problem_argument(["prog", "--create-issues"]))

    def test_flag_with_no_value_exits(self):
        with self.assertRaises(SystemExit):
            problem_argument(["prog", "--problem"])
