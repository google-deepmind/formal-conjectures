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

"""Offline tests for reading this repository's own Lean source.

Every case pins a failure a real import produced, or a rule whose violation
would copy source that elaborates but poses the wrong problem.
"""

import unittest
from unittest import mock

import fc_source
from fc_source import (
    answer_spans,
    file_scoped_preamble,
    hoist_answers,
    replace_proof_with_sorry,
    strip_decorations,
)


class HoistTest(unittest.TestCase):
    """Slot types come from the elaborated environment."""

    def test_slot_takes_the_environment_type(self):
        stmt, holes = hoist_answers(
            "theorem t : answer(sorry) ↔ ∀ n, n ≤ n := by\n  sorry", "t", ["Prop"]
        )
        self.assertIn("t_answer", stmt)
        self.assertEqual(
            holes[0].declaration(), "noncomputable def t_answer : Prop := sorry"
        )

    def test_erased_slot_is_prop_by_the_elaborators_rule(self):
        # The default `alwaysTrue` setting erases a slot iff its expected
        # type is Prop, so a missing annotation names the type exactly.
        _, holes = hoist_answers("theorem t : answer(sorry) ↔ P := by\n  sorry", "t", [])
        self.assertEqual(
            holes[0].declaration(), "noncomputable def t_answer : Prop := sorry"
        )

    def test_mixed_prop_and_typed_slots_are_refused(self):
        with self.assertRaises(SystemExit):
            hoist_answers(
                "theorem t : answer(sorry) ∧ (answer(sorry) = 3) := by\n  sorry",
                "t",
                ["Nat"],
            )

    def test_non_prop_type_is_read_not_guessed(self):
        _, holes = hoist_answers(
            "theorem t : sSup S = answer(sorry) := by\n  sorry", "t", ["ENNReal"]
        )
        self.assertEqual(holes[0].type, "ENNReal")

    def test_override_wins(self):
        _, holes = hoist_answers(
            "theorem t : sSup S = answer(sorry) := by\n  sorry", "t", ["ENNReal"], "ℝ"
        )
        self.assertEqual(holes[0].type, "ℝ")

    def test_differing_slot_types_are_refused(self):
        # Matching types to positions would be a guess.
        with self.assertRaises(SystemExit):
            hoist_answers(
                "theorem t : answer(sorry) = answer(sorry) := by\n  sorry",
                "t",
                ["Nat", "Int"],
            )

    def test_no_slot_is_left_alone(self):
        stmt, holes = hoist_answers("theorem t : True := by\n  sorry", "t", [])
        self.assertEqual(holes, [])

    def test_fixed_answer_is_not_turned_into_a_hole(self):
        original = "theorem t : IsGLB S answer(2) := by\n  sorry"
        unchanged, holes = hoist_answers(original, "t", ["ENNReal"])
        self.assertEqual(unchanged, original)
        self.assertEqual(holes, [])

    def test_nested_answer_term_is_one_balanced_slot(self):
        calls = answer_spans("theorem t : f answer((fun x => x) (g 2)) := by\n  sorry")
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][2], "(fun x => x) (g 2)")

    def test_answer_text_in_comments_and_strings_is_ignored(self):
        calls = answer_spans(
            '-- answer(1)\ntheorem t : p "answer(2)" answer(3) := by sorry'
        )
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][2], "3")


class PreambleTest(unittest.TestCase):
    """Only directives in force at the statement are carried."""

    def test_variable_in_a_closed_section_is_dropped(self):
        lines = [
            "section S",
            "variable {n : Nat}",
            "end S",
            "",
            "open Nat",
            "",
            "theorem t : True := trivial",
        ]
        pre, ns = file_scoped_preamble(lines, 7)
        self.assertEqual(pre, ["open Nat"])
        self.assertEqual(ns, [])

    def test_namespace_stack_is_reported(self):
        lines = ["namespace A", "open Nat", "theorem t : True := trivial"]
        pre, ns = file_scoped_preamble(lines, 3)
        self.assertEqual(pre, ["open Nat"])
        self.assertEqual(ns, ["A"])

    def test_directive_inside_a_comment_is_not_a_directive(self):
        lines = ["/--", "open the door", "-/", "theorem t : True := trivial"]
        pre, _ = file_scoped_preamble(lines, 4)
        self.assertEqual(pre, [])


class StatementTest(unittest.TestCase):
    def test_proof_is_replaced_but_statement_kept(self):
        out = replace_proof_with_sorry(
            "theorem t : True := by\n  have h := trivial\n  exact h"
        )
        self.assertIn("theorem t : True", out)
        self.assertNotIn("have h", out)
        self.assertTrue(out.rstrip().endswith("sorry"))

    def test_term_mode_proof_is_replaced_too(self):
        out = replace_proof_with_sorry("theorem t : True := trivial")
        self.assertNotIn("trivial", out)
        self.assertTrue(out.rstrip().endswith("sorry"))

    def test_structure_literal_assign_is_statement_text(self):
        # `{ a := 1 }` lives inside brackets; only the top-level `:=` starts
        # the proof, so the statement survives intact.
        out = replace_proof_with_sorry("theorem t : F { a := 1 } := ⟨rfl⟩")
        self.assertIn("F { a := 1 }", out)
        self.assertNotIn("⟨rfl⟩", out)
        self.assertTrue(out.rstrip().endswith("sorry"))

    def test_autoparam_default_is_statement_text(self):
        # An autoParam binder carries `:= by` inside its parentheses; the
        # proof is the top-level one.
        out = replace_proof_with_sorry(
            "theorem t (h : Fact (1 < 2) := by norm_num) : True := by trivial"
        )
        self.assertIn(":= by norm_num", out)
        self.assertNotIn("trivial", out)

    def test_two_top_level_assigns_are_refused(self):
        with self.assertRaises(SystemExit):
            replace_proof_with_sorry("def t : Nat := f := g")

    def test_a_line_comment_between_docstring_and_attribute_is_stripped(self):
        # Erdos 918 writes a `--` formalisation note there. One anchored pass
        # each left `@[category research open]` on the statement, and Lean
        # parsed as far as the `open` inside it.
        out = strip_decorations(
            "/-- doc -/\n-- note\n@[category research open, AMS 5]\n"
            "theorem t : True := by\n  sorry"
        )
        self.assertTrue(out.startswith("theorem"))

    def test_open_in_survives_stripping(self):
        # It binds to the declaration, and it sits above the docstring.
        out = strip_decorations(
            "open scoped Classical in\n/-- doc -/\n@[category research open]\n"
            "theorem t : True := by\n  sorry"
        )
        self.assertTrue(out.startswith("open scoped Classical in\ntheorem"))

    def test_decorations_are_stripped_from_the_target(self):
        out = strip_decorations(
            "/-- doc -/\n@[category research open]\ntheorem t : True := by\n  sorry"
        )
        self.assertTrue(out.startswith("theorem"))


class DocstringReferenceTest(unittest.TestCase):
    """The source citation is read from Formal Conjectures, not copied.

    A hand-kept copy drifts. The Margulis module's docstring pins
    `arxiv/2504.17644v3`; the problem file that used to carry the same
    citation had the unversioned URL, so the copy was already less exact
    than the docstring it was copied from.
    """

    def test_the_first_reference_link_is_the_citation(self):
        doc = (
            "/-!\n# Erdős Problem 1038\n\n*Reference:*\n"
            " - [erdosproblems.com/1038](https://www.erdosproblems.com/1038)\n"
            " - [Tao25] a blog post (https://example.com/other)\n-/"
        )
        self.assertEqual(
            fc_source.docstring_reference(doc), "https://www.erdosproblems.com/1038"
        )

    def test_an_arxiv_version_suffix_is_preserved(self):
        doc = "/-!\n*Reference:* [arxiv/2504.17644v3](https://arxiv.org/abs/2504.17644v3)\n-/"
        self.assertEqual(
            fc_source.docstring_reference(doc), "https://arxiv.org/abs/2504.17644v3"
        )

    def test_links_above_the_reference_line_are_not_the_citation(self):
        doc = "/-!\n# A problem\n\nSee [Mathlib](https://leanprover-community.github.io).\n-/"
        self.assertEqual(fc_source.docstring_reference(doc), "")

    def test_a_module_without_a_docstring_has_no_citation(self):
        self.assertEqual(fc_source.docstring_reference(""), "")


class ModuleNameCodecTest(unittest.TestCase):
    """`module_name` and `module_source_path` are inverse on real modules."""

    def test_a_guillemet_component_keeps_its_dots(self):
        self.assertEqual(
            fc_source.split_module(
                "FormalConjectures.Arxiv.«0912.2382».CurlingNumberConjecture"
            ),
            ["FormalConjectures", "Arxiv", "0912.2382", "CurlingNumberConjecture"],
        )

    def test_a_dotted_final_component_keeps_its_tail(self):
        # `with_suffix` would have turned `«2501.03234»` into `«2501.lean`.
        path = fc_source.module_source_path(
            "FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS"
        )
        self.assertEqual(path.name, "ArithmeticSumS.lean")
        self.assertEqual(path.parent.name, "2501.03234")

    def test_a_malformed_name_is_refused(self):
        with self.assertRaises(SystemExit):
            fc_source.split_module("FormalConjectures.«unterminated")

    def test_every_real_module_round_trips(self):
        # The property that keeps the codec from drifting again: for every
        # file the importer can name, decoding the name reaches the file.
        for src in fc_source.SOURCE_DIRS:
            for path in src.rglob("*.lean"):
                rel = path.relative_to(fc_source.ROOT)
                with self.subTest(module=str(rel)):
                    self.assertEqual(
                        fc_source.module_source_path(fc_source.module_name(rel)), path
                    )


class QualifiedResolutionTest(unittest.TestCase):
    """Qualified requests resolve through the namespace stack."""

    def test_the_bare_colliding_name_is_ambiguous(self):
        with self.assertRaises(SystemExit) as ctx:
            fc_source.find_declaration("conjecture")
        self.assertIn("ambiguous", str(ctx.exception))

    def test_each_qualified_name_reaches_its_own_file(self):
        for qualified, filename in (
            ("OeisA303656.conjecture", "303656.lean"),
            ("OeisA308734.conjecture", "308734.lean"),
        ):
            with self.subTest(qualified=qualified):
                path, _, _, _ = fc_source.find_declaration(qualified)
                self.assertEqual(path.name, filename)

    def test_a_declared_name_with_dots_still_resolves(self):
        # The declared name itself contains dots; no namespace split applies.
        path, _, _, _ = fc_source.find_declaration(
            "erdos_125.variants.positive_unequal_density"
        )
        self.assertEqual(path.name, "125.lean")

    def test_longest_declared_suffix_wins(self):
        # `Erdos125.erdos_125.variants.positive_unequal_density`: the first
        # component is the namespace, the rest is the declared name.
        path, _, _, _ = fc_source.find_declaration(
            "Erdos125.erdos_125.variants.positive_unequal_density"
        )
        self.assertEqual(path.name, "125.lean")


class FlattenDeclaredNameTest(unittest.TestCase):
    """Dotted declaration names are restated as slugs for the generator."""

    def test_the_declaring_occurrence_is_renamed(self):
        name, statement = fc_source.flatten_declared_name(
            "erdos_100.variants.strong",
            "theorem erdos_100.variants.strong : True := by\n  sorry",
        )
        self.assertEqual(name, "erdos_100_variants_strong")
        self.assertEqual(
            statement, "theorem erdos_100_variants_strong : True := by\n  sorry"
        )

    def test_a_prefix_line_does_not_confuse_the_rename(self):
        # `open X in` binds to the declaration below and travels with the
        # slice; the declaring line is not the first line.
        name, statement = fc_source.flatten_declared_name(
            "a.b", "open Nat in\ntheorem a.b : True := by\n  sorry"
        )
        self.assertEqual(name, "a_b")
        self.assertIn("theorem a_b :", statement)

    def test_an_absent_declaration_is_refused(self):
        with self.assertRaises(SystemExit):
            fc_source.flatten_declared_name("a.b", "theorem c.d : True := sorry")


class PreambleNotationTest(unittest.TestCase):
    """File-scoped notation and macros travel with the preamble."""

    def test_local_notation_is_kept(self):
        # Irrational.lean: dropping `local notation "e" => exp 1` left `e`
        # to auto-bind as an implicit at FC pins and fail at LeanEval's.
        lines = ['local notation "e" => exp 1', "theorem t : True := trivial"]
        pre, _ = file_scoped_preamble(lines, 2)
        self.assertEqual(pre, ['local notation "e" => exp 1'])

    def test_a_macro_keeps_its_indented_body(self):
        # Poincare.lean: the 𝕊ⁿ macro's body is on the next line; one kept
        # line would be broken syntax.
        lines = [
            'local macro:max "𝕊" noWs n:superscript(term) : term =>',
            "  `(Metric.sphere 0 1)",
            "theorem t : True := trivial",
        ]
        pre, _ = file_scoped_preamble(lines, 3)
        self.assertEqual(len(pre), 1)
        self.assertIn("`(Metric.sphere 0 1)", pre[0])

    def test_noncomputable_section_is_restated(self):
        # OpenQuantumProblems/23: a copied def that was total inside
        # `noncomputable section` fails to compile outside it.
        lines = ["noncomputable section", "theorem t : True := trivial"]
        pre, _ = file_scoped_preamble(lines, 2)
        self.assertIn("noncomputable section", pre)

    def test_a_closed_noncomputable_section_is_not_restated(self):
        lines = ["noncomputable section", "end", "theorem t : True := trivial"]
        pre, _ = file_scoped_preamble(lines, 3)
        self.assertNotIn("noncomputable section", pre)


class AscribedSlotTest(unittest.TestCase):
    """`(answer(sorry) : T)` states its own type at its own position."""

    def test_the_ascription_wins_over_the_erasure_rule(self):
        # Erdos332: the annotation for an ascribed-and-applied slot does not
        # survive elaboration, so the environment reports nothing and the
        # erasure rule would call it Prop.
        statement = (
            "theorem erdos_332 (A : Set ℕ) : "
            "(answer(sorry) : Set ℕ → Prop) A → True := by\n  sorry"
        )
        _, holes = hoist_answers(statement, "erdos_332", [])
        self.assertEqual(holes[0].type, "Set ℕ → Prop")

    def test_a_nested_paren_type_stays_whole(self):
        statement = "theorem t : (answer(sorry) : (ℕ → ℕ) → Prop) f := by\n  sorry"
        _, holes = hoist_answers(statement, "t", [])
        self.assertEqual(holes[0].type, "(ℕ → ℕ) → Prop")

    def test_an_unascribed_slot_still_follows_the_erasure_rule(self):
        statement = "theorem t : answer(sorry) ↔ True := by\n  sorry"
        _, holes = hoist_answers(statement, "t", [])
        self.assertEqual(holes[0].type, "Prop")


class NotationBlocksTest(unittest.TestCase):
    """FC-defined notation is copied only where it was in force."""

    def _with_commands(self, commands):
        return mock.patch.object(
            fc_source, "fc_notation_commands", return_value=commands
        )

    def test_a_scoped_notation_needs_its_namespace_opened(self):
        commands = [
            (["ℝ²"], 'scoped[EuclideanGeometry] notation "ℝ²" => E', "EuclideanGeometry", True),
        ]
        with self._with_commands(commands):
            self.assertEqual(
                fc_source.notation_blocks(["def f : ℝ² := sorry"], {"EuclideanGeometry"}),
                ['scoped[EuclideanGeometry] notation "ℝ²" => E'],
            )
            # Green9's `⊆` false positive: same token, namespace never opened.
            self.assertEqual(
                fc_source.notation_blocks(["def f : ℝ² := sorry"], set()), []
            )

    def test_a_shared_global_notation_is_copied_as_local(self):
        # Global would be declared in ChallengeDeps and re-extracted into
        # the importing file too; `local` keeps each copy to its own file.
        commands = [(["≪"], 'notation g " ≪ " f => IsBigO g f', None, True)]
        with self._with_commands(commands):
            self.assertEqual(
                fc_source.notation_blocks(["theorem t : a ≪ b := sorry"], set()),
                ['local notation g " ≪ " f => IsBigO g f'],
            )

    def test_a_problem_module_global_notation_is_never_copied(self):
        commands = [(["≪"], 'notation g " ≪ " f => X g f', None, False)]
        with self._with_commands(commands):
            self.assertEqual(
                fc_source.notation_blocks(["theorem t : a ≪ b := sorry"], set()), []
            )

    def test_an_unused_token_is_not_copied(self):
        commands = [(["ℝ²"], 'notation "ℝ²" => E', None, True)]
        with self._with_commands(commands):
            self.assertEqual(fc_source.notation_blocks(["theorem t : True"], set()), [])


class LocaliseNotationTest(unittest.TestCase):
    def test_a_global_notation_becomes_local(self):
        self.assertEqual(
            fc_source.localise_notation(['notation "R(" k ")" => f k']),
            ['local notation "R(" k ")" => f k'],
        )

    def test_quot_precheck_travels_with_the_notation(self):
        out = fc_source.localise_notation(
            ["set_option quotPrecheck false", 'local notation "A" => s']
        )
        self.assertEqual(
            out[1],
            'set_option quotPrecheck false in\nlocal notation "A" => s',
        )

    def test_other_preamble_lines_pass_through(self):
        self.assertEqual(
            fc_source.localise_notation(["open Nat", "variable (n : Nat)"]),
            ["open Nat", "variable (n : Nat)"],
        )


if __name__ == "__main__":
    unittest.main()
