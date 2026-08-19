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

"""Offline tests for `make_comparator_workspace.py`.

Every case here pins a failure the first real workspace build produced, or a
rule whose violation would generate a workspace that builds but poses the
wrong problem. The build itself is the comparator's job, not these tests'.
"""

import contextlib
import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest import mock

import make_comparator_workspace as mcw
from make_comparator_workspace import (
    answer_spans,
    challenge_deps,
    file_scoped_preamble,
    hoist_answers,
    load_manifest,
    pins,
    replace_proof_with_sorry,
    strip_decorations,
    strip_fc_attributes,
    unwrap_answers,
    write_workspace,
)


class HoistTest(unittest.TestCase):
    """Slot types come from the elaborated environment."""

    def test_slot_takes_the_environment_type(self):
        stmt, holes = hoist_answers(
            "theorem t : answer(sorry) ↔ ∀ n, n ≤ n := by\n  sorry", "t", ["Prop"]
        )
        self.assertIn("t_answer", stmt)
        self.assertIn("noncomputable def t_answer : Prop := sorry", holes)

    def test_erased_slot_is_prop_by_the_elaborators_rule(self):
        # The default `alwaysTrue` setting erases a slot iff its expected
        # type is Prop, so a missing annotation names the type exactly.
        _, holes = hoist_answers(
            "theorem t : answer(sorry) ↔ P := by\n  sorry", "t", []
        )
        self.assertIn("noncomputable def t_answer : Prop := sorry", holes)

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
        self.assertIn("t_answer : ENNReal", holes[0])

    def test_override_wins(self):
        _, holes = hoist_answers(
            "theorem t : sSup S = answer(sorry) := by\n  sorry", "t", ["ENNReal"], "ℝ"
        )
        self.assertIn("t_answer : ℝ", holes[0])

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

    def test_term_proof_with_a_structure_literal_is_refused(self):
        # The statement's own `:=` cannot be told from the proof's, and
        # cutting at the wrong one truncates the statement.
        with self.assertRaises(SystemExit):
            replace_proof_with_sorry("theorem t : F { a := 1 } := ⟨rfl⟩")

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


class TemplateTest(unittest.TestCase):
    def test_workspace_test_template_exists_and_is_the_runner(self):
        # The generator copies this file into every workspace; a missing or
        # gutted template would only surface at `lake test` time, elsewhere.
        text = (mcw.COMPARATOR_DIR / "templates" / "WorkspaceTest.lean").read_text()
        self.assertIn("def main", text)
        self.assertIn("COMPARATOR_BIN", text)


class ManifestTest(unittest.TestCase):
    """A manifest supplies what the Lean source cannot."""

    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self._saved = mcw.MANIFEST_DIR
        mcw.MANIFEST_DIR = pathlib.Path(self._dir.name)

    def tearDown(self):
        mcw.MANIFEST_DIR = self._saved
        self._dir.cleanup()

    def write(self, name, body):
        (mcw.MANIFEST_DIR / name).write_text(body)

    def test_absent_manifest_is_not_an_error(self):
        # Most statements need none, and the generator works without one.
        self.assertEqual(load_manifest("no_such_problem"), {})

    def test_fields_are_read(self):
        self.write("p.toml", 'id = "p"\ndeclaration = "d"\nanswer_type = "ENNReal"\n')
        self.assertEqual(load_manifest("p")["answer_type"], "ENNReal")

    def test_id_must_match_the_filename(self):
        # The filename is what the generator looks up, so a disagreeing `id`
        # would silently name a workspace directory nobody asked for.
        self.write("p.toml", 'id = "other"\ndeclaration = "d"\n')
        with self.assertRaises(SystemExit):
            load_manifest("p")

    def test_declaration_is_required(self):
        self.write("p.toml", 'id = "p"\n')
        with self.assertRaises(SystemExit):
            load_manifest("p")


class OutputTest(unittest.TestCase):
    def test_existing_workspace_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp) / "workspace"
            target.mkdir()
            sentinel = target / "keep.txt"
            sentinel.write_text("keep", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "refusing to overwrite"):
                write_workspace(target, {"Challenge.lean": "theorem t : True"})
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")

    def test_failed_write_leaves_no_partial_workspace(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            target = root / "workspace"
            with mock.patch.object(
                pathlib.Path, "write_text", side_effect=OSError("disk error")
            ):
                with self.assertRaisesRegex(OSError, "disk error"):
                    write_workspace(target, {"Challenge.lean": "theorem t : True"})
            self.assertFalse(target.exists())
            self.assertEqual(list(root.iterdir()), [])


class PinTest(unittest.TestCase):
    def test_changed_source_is_refused(self):
        saved_root = mcw.ROOT
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            mcw.ROOT = root
            (root / "lake-manifest.json").write_text(
                json.dumps(
                    {
                        "packages": [{"name": "mathlib", "rev": "b" * 40}],
                    }
                ),
                encoding="utf-8",
            )
            results = [
                subprocess.CompletedProcess([], 0, stdout="a" * 40 + "\n"),
                subprocess.CompletedProcess([], 1),
            ]
            try:
                with mock.patch.object(mcw.subprocess, "run", side_effect=results):
                    with self.assertRaisesRegex(SystemExit, "differs from pinned"):
                        pins(pathlib.Path("FormalConjectures/Example.lean"))
            finally:
                mcw.ROOT = saved_root


@contextlib.contextmanager
def _root_at(directory):
    """Point the module's ROOT at a fixture tree.

    `challenge_deps` records each copied declaration's path relative to ROOT,
    so a fixture written outside it cannot be described.
    """
    saved = mcw.ROOT
    mcw.ROOT = pathlib.Path(directory)
    try:
        yield
    finally:
        mcw.ROOT = saved


class MathlibOnlyChallengeTest(unittest.TestCase):
    """The closure travels with the workspace, so copying has to be right.

    Each case here is a defect a generated workspace actually had, found by
    elaborating it rather than by reading it.
    """

    def test_answer_with_a_value_is_unwrapped(self):
        # `answer` is this repository's elaborator. `hoist_answers` removes the
        # `answer(sorry)` slots; `conjecture327` is `research solved` and
        # carries `answer(False)`, which reached Challenge.lean verbatim and
        # failed to parse against Mathlib alone.
        self.assertEqual(
            unwrap_answers("theorem t : answer(False) ↔ P := by\n  sorry"),
            "theorem t : (False) ↔ P := by\n  sorry",
        )

    def test_unwrapping_keeps_a_parenthesised_argument_whole(self):
        self.assertEqual(unwrap_answers("answer(f (n + 1))"), "(f (n + 1))")

    def test_only_this_repository_s_attributes_are_dropped(self):
        # `strip_decorations` clears every attribute off the target statement.
        # A copied dependency keeps the rest: dropping `simp` or `reducible`
        # changes how the declarations after it in the closure elaborate.
        self.assertEqual(
            strip_fc_attributes("@[simp, category API, AMS 11]\ntheorem t : P"),
            "@[simp]\ntheorem t : P",
        )
        self.assertEqual(
            strip_fc_attributes("@[category API]\ntheorem t : P"), "theorem t : P"
        )
        self.assertEqual(strip_fc_attributes("@[simp]\ndef f := 1"), "@[simp]\ndef f := 1")

    def test_a_generated_constant_with_no_copied_ancestor_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "no copied ancestor"):
            challenge_deps([], ["Foo.bar._proof_1"], "t")

    def test_a_generated_constant_under_a_copied_parent_is_accepted(self):
        # `_proof_1` and `.match_1` have no source: copying the parent
        # declaration regenerates them, so they are not an error.
        deps = [
            {
                "name": "Foo.bar",
                "module": "FormalConjectures.Example",
                "range": {"startLine": 1, "endLine": 1, "endColumn": None},
            }
        ]
        with (
            mock.patch.object(mcw, "module_source_path") as resolve,
            tempfile.TemporaryDirectory() as tmp,
            _root_at(tmp),
        ):
            source = pathlib.Path(tmp) / "Example.lean"
            source.write_text("def Foo.bar := 1\n", encoding="utf-8")
            resolve.return_value = source
            out = challenge_deps(deps, ["Foo.bar._proof_1"], "t")
        self.assertIn("import Mathlib", out)
        self.assertIn("def Foo.bar := 1", out)

    def test_a_declaration_inside_another_s_range_is_not_copied_twice(self):
        # `EdgeN.mk` covers line 88 of a structure spanning 83 to 93, and
        # `pmSumListAux._sparseCasesOn_1` has exactly its parent's range.
        # Copying either in its own right duplicated a declaration or sliced a
        # fragment of one.
        def span(name, lo, hi):
            return {
                "name": name,
                "module": "FormalConjectures.Example",
                "range": {"startLine": lo, "endLine": hi, "endColumn": None},
            }

        deps = [
            span("Foo.EdgeN.mk", 2, 2),
            span("Foo.EdgeN", 1, 3),
            span("Foo.aux._sparseCasesOn_1", 5, 5),
            span("Foo.aux", 5, 5),
        ]
        with (
            mock.patch.object(mcw, "module_source_path") as resolve,
            tempfile.TemporaryDirectory() as tmp,
            _root_at(tmp),
        ):
            source = pathlib.Path(tmp) / "Example.lean"
            source.write_text(
                "structure EdgeN where\n  u : Nat\n  deriving DecidableEq\n"
                "\ndef aux := 1\n",
                encoding="utf-8",
            )
            resolve.return_value = source
            out = challenge_deps(deps, [], "t")
        self.assertIn("Foo.EdgeN`", out)
        self.assertNotIn("Foo.EdgeN.mk`", out)
        self.assertIn("Foo.aux`", out)
        self.assertNotIn("_sparseCasesOn_1`", out)

    def test_an_opened_namespace_no_dependency_declares_is_created(self):
        # Challenge.lean reopens the namespace stack its target sat in. With
        # the problem's module no longer imported, `open Grimm` is an error
        # unless something declares that namespace.
        out = challenge_deps([], [], "grimm_conjecture", ["Grimm"])
        self.assertIn("namespace Grimm\nend Grimm", out)

    def test_a_namespace_a_dependency_declares_is_not_restated(self):
        deps = [
            {
                "name": "Grimm.helper",
                "module": "FormalConjectures.Example",
                "range": {"startLine": 1, "endLine": 1, "endColumn": None},
            }
        ]
        with (
            mock.patch.object(mcw, "module_source_path") as resolve,
            tempfile.TemporaryDirectory() as tmp,
            _root_at(tmp),
        ):
            source = pathlib.Path(tmp) / "Example.lean"
            source.write_text("def Grimm.helper := 1\n", encoding="utf-8")
            resolve.return_value = source
            out = challenge_deps(deps, [], "t", ["Grimm"])
        self.assertNotIn("namespace Grimm\nend Grimm", out)


if __name__ == "__main__":
    unittest.main()
