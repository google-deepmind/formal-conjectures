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

"""Offline tests for the Formal Conjectures side of the LeanEval importer.

Every case here pins a failure the first real workspace build produced, or a
rule whose violation would produce a marked-up module that elaborates but poses
the wrong problem. The build itself is the comparator's job, not these tests'.
"""

import contextlib
import inspect
import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest import mock

import fc_leaneval_importer as importer
import fc_source
from fc_leaneval_importer import closure_region, load_manifest
from fc_source import pins, strip_fc_attributes, unwrap_answers


class ProblemFileTest(unittest.TestCase):
    """An FC problem file supplies what the Lean source cannot."""

    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self._saved = importer.MANIFEST_DIR
        importer.MANIFEST_DIR = pathlib.Path(self._dir.name)

    def tearDown(self):
        importer.MANIFEST_DIR = self._saved
        self._dir.cleanup()

    def write(self, name, body):
        (importer.MANIFEST_DIR / name).write_text(body)

    def test_absent_problem_file_is_not_an_error(self):
        # Most statements need none, and the importer works without one.
        self.assertEqual(load_manifest("no_such_problem"), {})

    def test_fields_are_read(self):
        self.write("p.toml", 'id = "p"\ndeclaration = "d"\nmodule = "m.lean"\n')
        self.assertEqual(load_manifest("p")["module"], "m.lean")

    def test_unknown_keys_are_refused(self):
        # A field no code consumes is a record nobody can check: it reads as
        # configuration while silently doing nothing.
        self.write("p.toml", 'id = "p"\ndeclaration = "d"\nanswer_type = "ENNReal"\n')
        with self.assertRaisesRegex(SystemExit, "keys nothing reads"):
            load_manifest("p")

    def test_id_must_match_the_filename(self):
        # The filename is what the importer looks up, so a disagreeing `id`
        # would silently name a workspace directory nobody asked for.
        self.write("p.toml", 'id = "other"\ndeclaration = "d"\n')
        with self.assertRaises(SystemExit):
            load_manifest("p")

    def test_declaration_is_required(self):
        self.write("p.toml", 'id = "p"\n')
        with self.assertRaises(SystemExit):
            load_manifest("p")


class PinTest(unittest.TestCase):
    """Every path the importer read is held to the one source revision."""

    @contextlib.contextmanager
    def _pins_repo(self, git_results):
        saved_root = fc_source.ROOT
        fc_source._base_pins.cache_clear()
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fc_source.ROOT = root
            (root / "lake-manifest.json").write_text(
                json.dumps({"packages": [{"name": "mathlib", "rev": "b" * 40}]}),
                encoding="utf-8",
            )
            try:
                with mock.patch.object(
                    fc_source.subprocess, "run", side_effect=git_results
                ):
                    yield
            finally:
                fc_source.ROOT = saved_root
                fc_source._base_pins.cache_clear()

    def test_changed_source_is_refused(self):
        path = "FormalConjectures/Example.lean"
        results = [
            subprocess.CompletedProcess([], 0, stdout="a" * 40 + "\n"),
            subprocess.CompletedProcess([], 0, stdout=path + "\n"),
            subprocess.CompletedProcess([], 1),
            subprocess.CompletedProcess([], 0, stdout=path + "\n"),
        ]
        with self._pins_repo(results):
            with self.assertRaisesRegex(SystemExit, "differs from pinned"):
                pins(pathlib.Path(path))

    def test_a_path_the_revision_does_not_track_is_refused(self):
        # `git diff` is silent about untracked files, so a dependency read
        # from a file the pinned revision has never seen must fail on the
        # tracking check, not pass by omission.
        results = [
            subprocess.CompletedProcess([], 0, stdout="a" * 40 + "\n"),
            subprocess.CompletedProcess([], 0, stdout="\n"),
        ]
        with self._pins_repo(results):
            with self.assertRaisesRegex(SystemExit, "not tracked at pinned"):
                pins(pathlib.Path("FormalConjectures/New.lean"))

    def test_the_toolchain_is_not_held_to_the_pin(self):
        # A toolchain bump edits `lean-toolchain` and `lake-manifest.json`.
        # Those describe the environment the facts were read in, which the
        # record states as an observation. Holding them to the merge base
        # would make a bump the one change that cannot pass this check.
        import fc_leaneval_importer as importer_module

        source = inspect.getsource(importer_module.import_problem)
        self.assertNotIn("lean-toolchain", source)
        self.assertNotIn("lake-manifest.json", source)

    def test_a_dirty_dependency_fails_even_with_a_clean_target(self):
        # The reviewer's mixed state: target at the pin, dependency edited in
        # the working tree. One diff over every read path refuses it.
        target = "FormalConjectures/Target.lean"
        dep = "FormalConjectures/Dep.lean"
        results = [
            subprocess.CompletedProcess([], 0, stdout="a" * 40 + "\n"),
            subprocess.CompletedProcess([], 0, stdout=f"{dep}\n{target}\n"),
            subprocess.CompletedProcess([], 1),
            subprocess.CompletedProcess([], 0, stdout=dep + "\n"),
        ]
        with self._pins_repo(results):
            with self.assertRaisesRegex(SystemExit, "Dep.lean differs from pinned"):
                pins([pathlib.Path(target), pathlib.Path(dep)])


@contextlib.contextmanager
def _root_at(directory):
    """Point the module's ROOT at a fixture tree.

    `closure_region` records each copied declaration's path relative to ROOT,
    so a fixture written outside it cannot be described.
    """
    saved = importer.ROOT
    importer.ROOT = pathlib.Path(directory)
    try:
        yield
    finally:
        importer.ROOT = saved


class MathlibOnlyClosureTest(unittest.TestCase):
    """The closure travels with the module, so copying has to be right.

    Each case here is a defect a generated workspace actually had, found by
    elaborating it rather than by reading it.
    """

    def test_answer_with_a_value_is_unwrapped(self):
        # `answer` is this repository's elaborator. `hoist_answers` removes the
        # `answer(sorry)` slots; `conjecture327` is `research solved` and
        # carries `answer(False)`, which reached the module verbatim and
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
        self.assertEqual(
            strip_fc_attributes("@[simp]\ndef f := 1"), "@[simp]\ndef f := 1"
        )

    def test_a_generated_constant_with_no_copied_ancestor_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "no copied ancestor"):
            closure_region([], ["Foo.bar._proof_1"], "t")

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
            mock.patch.object(importer, "module_source_path") as resolve,
            tempfile.TemporaryDirectory() as tmp,
            _root_at(tmp),
        ):
            source = pathlib.Path(tmp) / "Example.lean"
            source.write_text("def Foo.bar := 1\n", encoding="utf-8")
            resolve.return_value = source
            out, copied, records = closure_region(deps, ["Foo.bar._proof_1"], "t")
        self.assertIn("def Foo.bar := 1", out)
        self.assertIn("noncomputable section", out)
        self.assertEqual(copied, [("Foo.bar", "def Foo.bar := 1")])
        # The sidecar's record of the same copy: the emitted slice, located
        # and digested, so the provenance chain reaches each dependency.
        self.assertEqual(len(records), 1)
        record = records[0]
        self.assertEqual(record["declaration"], "Foo.bar")
        self.assertEqual(record["module"], "FormalConjectures.Example")
        self.assertEqual(record["path"], "Example.lean")
        self.assertEqual(record["range"]["startLine"], 1)
        self.assertEqual(len(record["content_sha256"]), 64)

    def test_an_explicit_source_only_dependency_carries_its_closure(self):
        facts = fc_source.FactsRecord.from_payload(
            {
                "declaration": "Foo.opaqueLemma",
                "name": "Foo.opaqueLemma",
                "category": None,
                "range": {"startLine": 2, "endLine": 2, "endColumn": None},
                "binders": [],
                "answerTypes": [],
                "dependencies": [
                    {
                        "name": "Foo.Predicate",
                        "module": "FormalConjectures.Example",
                        "range": {"startLine": 1, "endLine": 1, "endColumn": None},
                    }
                ],
                "generatedDependencies": ["Foo.opaqueLemma._proof_1"],
            },
            "Foo.opaqueLemma",
        )
        with tempfile.TemporaryDirectory() as tmp, _root_at(tmp):
            module = pathlib.Path(tmp) / "FormalConjectures" / "Example.lean"
            module.parent.mkdir(parents=True)
            module.write_text("def Predicate := True\ntheorem opaqueLemma : Predicate := by trivial\n")
            with mock.patch.object(importer, "elaborator_facts", return_value=facts):
                records, generated = importer.explicit_copy_dependencies(
                    {
                        "copy_dependencies": [
                            {
                                "declaration": "Foo.opaqueLemma",
                                "module": "FormalConjectures/Example.lean",
                            }
                        ]
                    }
                )
        self.assertEqual(
            [record["name"] for record in records],
            ["Foo.Predicate", "Foo.opaqueLemma"],
        )
        self.assertEqual(generated, ["Foo.opaqueLemma._proof_1"])

    def test_explicit_source_only_dependency_rejects_extra_fields(self):
        with self.assertRaisesRegex(SystemExit, "must contain exactly"):
            importer.explicit_copy_dependencies(
                {
                    "copy_dependencies": [
                        {
                            "declaration": "Foo.opaqueLemma",
                            "module": "FormalConjectures/Example.lean",
                            "guess": True,
                        }
                    ]
                }
            )

    def test_explicit_source_only_dependency_stays_in_a_source_tree(self):
        with self.assertRaisesRegex(SystemExit, "must stay under a source tree"):
            importer.explicit_copy_dependencies(
                {
                    "copy_dependencies": [
                        {
                            "declaration": "Foo.opaqueLemma",
                            "module": "../Elsewhere/Example.lean",
                        }
                    ]
                }
            )

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
            mock.patch.object(importer, "module_source_path") as resolve,
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
            out, _copied, _records = closure_region(deps, [], "t")
        self.assertIn("Foo.EdgeN`", out)
        self.assertNotIn("Foo.EdgeN.mk`", out)
        self.assertIn("Foo.aux`", out)
        self.assertNotIn("_sparseCasesOn_1`", out)

    def test_an_opened_namespace_no_dependency_declares_is_created(self):
        # The statement reopens the namespace stack its target sat in. With
        # the problem's module no longer imported, `open Grimm` is an error
        # unless something declares that namespace.
        out, _copied, _records = closure_region([], [], "grimm_conjecture", ["Grimm"])
        self.assertIn("namespace Grimm\nend Grimm", out)

    def test_namespaces_exist_before_any_copied_block_opens_them(self):
        deps = [
            {
                "name": "Grimm.helper",
                "module": "FormalConjectures.Example",
                "range": {"startLine": 1, "endLine": 1, "endColumn": None},
            }
        ]
        with (
            mock.patch.object(importer, "module_source_path") as resolve,
            tempfile.TemporaryDirectory() as tmp,
            _root_at(tmp),
        ):
            source = pathlib.Path(tmp) / "Example.lean"
            source.write_text("def Grimm.helper := 1\n", encoding="utf-8")
            resolve.return_value = source
            out, _copied, _records = closure_region(deps, [], "t", ["Grimm"])
        # The empty block that makes the namespace exist comes before any
        # copied block: a copied preamble may `open` it before anything
        # declares it. Redundant creation is harmless.
        self.assertLess(
            out.index("namespace Grimm\nend Grimm"), out.index("def Grimm.helper")
        )

    def test_the_closure_region_does_not_carry_the_import(self):
        # `import Mathlib` belongs to the module as a whole, and the generator
        # is what decides which emitted file carries it. A region that
        # restated it would put an import in the middle of a Lean file.
        out, _copied, _records = closure_region([], [], "t")
        self.assertNotIn("import", out)


if __name__ == "__main__":
    unittest.main()
