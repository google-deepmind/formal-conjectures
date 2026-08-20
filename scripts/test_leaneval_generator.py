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

"""Tests for the side of the seam that becomes a pinned dependency.

These cases describe what a Challenge/Solution/Submission workspace must look
like given a marked-up module and a manifest. They are written against nothing
but those two values on purpose: when `leanprover/lean-eval-generator` replaces
`scripts/leaneval_generator.py`, this file is what says whether the pinned
generator still produces what Formal Conjectures' import expects.
"""

import ast
import json
import pathlib
import unittest

import leaneval_generator as generator
from leaneval_generator import generate
from test_leaneval_interface import A_MODULE, a_manifest, a_target

# The modules that live beside the generator in `scripts/`. Anything the
# generator imports from here has to move with it into the pinned package.
LOCAL = {path.name for path in pathlib.Path(generator.__file__).parent.glob("*.py")}


def a_workspace(**overrides):
    return generate(A_MODULE, a_manifest(**overrides), a_target())


class SplitTest(unittest.TestCase):
    """One module in, four Lean files out, and the imports have to line up."""

    def test_the_closure_is_the_only_file_importing_mathlib(self):
        files = a_workspace()
        self.assertTrue(files["ChallengeDeps.lean"].startswith("import Mathlib\n"))
        self.assertIn("def Foo.bar := 1", files["ChallengeDeps.lean"])
        for name in ("Challenge.lean", "Solution.lean", "Submission.lean"):
            self.assertTrue(files[name].startswith("import ChallengeDeps"), name)

    def test_the_statement_text_is_identical_in_all_three_files(self):
        # The Solution adapter only pins the statement if the statement it
        # restates is the one the Challenge poses.
        files = a_workspace()
        statement = A_MODULE.statement
        self.assertIn(statement, files["Challenge.lean"])
        self.assertIn(statement, files["Submission.lean"])
        self.assertIn(statement.split(":= by")[0].rstrip(), files["Solution.lean"])

    def test_the_scope_is_restated_in_every_file_that_carries_the_statement(self):
        # `open Erdos` is file-scoped, so an import cannot carry it.
        files = a_workspace()
        for name in ("Challenge.lean", "Solution.lean", "Submission.lean"):
            self.assertIn("open Erdos", files[name], name)

    def test_the_submission_is_namespaced_away_from_the_trusted_names(self):
        submission = a_workspace()["Submission.lean"]
        self.assertIn("namespace Submission", submission)
        self.assertIn("end Submission", submission)

    def test_the_solution_delegates_the_hole_and_applies_the_arguments(self):
        solution = a_workspace()["Solution.lean"]
        # Reducible, so the unifier is certain to unfold the Solution's copy of
        # the hole into the Submission's when it checks the adapter.
        self.assertIn(
            "@[reducible] noncomputable def erdos_940_answer : ENNReal :=\n"
            "  Submission.erdos_940_answer",
            solution,
        )
        self.assertTrue(solution.rstrip().endswith("Submission.erdos_940 n"))

    def test_a_statement_with_no_arguments_is_not_applied_to_anything(self):
        # A `∀` binder in the conclusion is not a declaration parameter, and
        # applying one would fail to elaborate.
        solution = a_workspace(apply_arguments=())["Solution.lean"]
        self.assertTrue(solution.rstrip().endswith("Submission.erdos_940"))

    def test_a_workspace_with_no_hole_declares_no_definition_names(self):
        config = json.loads(a_workspace(holes=())["config.json"])
        self.assertNotIn("definition_names", config)

    def test_the_config_names_the_theorem_the_holes_and_the_axioms(self):
        config = json.loads(a_workspace()["config.json"])
        self.assertEqual(config["theorem_names"], ["erdos_940"])
        self.assertEqual(config["definition_names"], ["erdos_940_answer"])
        self.assertIn("propext", config["permitted_axioms"])
        self.assertNotIn("sorryAx", config["permitted_axioms"])

    def test_the_lakefile_pins_the_target_mathlib(self):
        # Not this repository's Mathlib: the workspace is built in lean-eval.
        lakefile = a_workspace()["lakefile.toml"]
        self.assertIn('rev = "' + "f" * 40 + '"', lakefile)
        self.assertEqual(lakefile.count("[[require]]"), 1)
        self.assertNotIn("formal-conjectures", lakefile)

    def test_the_package_name_is_an_identifier(self):
        files = generate(A_MODULE, a_manifest(id="erdos_940.variants.large_integers"), a_target())
        self.assertIn(
            'name = "erdos_940_variants_large_integers"', files["lakefile.toml"]
        )

    def test_the_toolchain_file_is_the_target_toolchain(self):
        self.assertEqual(a_workspace()["lean-toolchain"], "leanprover/lean4:v4.33.0\n")

    def test_nothing_in_the_workspace_carries_this_repositorys_toolchain(self):
        # A workspace built at FC's toolchain is not the artifact lean-eval
        # vendors, and shipping one would hide the pin gap the manifest states.
        files = a_workspace()
        self.assertNotIn("v4.27.0", files["lean-toolchain"])
        self.assertNotIn("v4.27.0", files["lakefile.toml"])


class ManifestPassThroughTest(unittest.TestCase):
    def test_the_workspace_carries_the_fc_commit_and_declaration(self):
        # lean-eval#536: each manifest records the FC source commit and
        # declaration id. This side supplies neither and edits neither.
        payload = json.loads(a_workspace()["manifest.json"])
        self.assertEqual(payload["source"]["commit"], "a" * 40)
        self.assertEqual(payload["source"]["declaration"], "erdos_940")

    def test_the_manifest_is_passed_through_unaltered(self):
        manifest = a_manifest()
        files = generate(A_MODULE, manifest, a_target())
        self.assertEqual(files["manifest.json"], manifest.to_json())


class SeamTest(unittest.TestCase):
    def test_the_generator_depends_on_the_interface_and_nothing_else_local(self):
        # The direction of the dependency is the whole point: a generator that
        # imported the importer could not be swapped for a pinned package.
        tree = ast.parse(pathlib.Path(generator.__file__).read_text(encoding="utf-8"))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module)
        local = {name for name in imported if pathlib.Path(f"{name}.py").name in LOCAL}
        self.assertEqual(local, {"leaneval_interface"})


class TemplateTest(unittest.TestCase):
    def test_workspace_test_template_exists_and_is_the_runner(self):
        # The generator copies this file into every workspace; a missing or
        # gutted template would only surface at `lake test` time, elsewhere.
        text = (generator.TEMPLATE_DIR / "WorkspaceTest.lean").read_text()
        self.assertIn("def main", text)
        self.assertIn("COMPARATOR_BIN", text)


if __name__ == "__main__":
    unittest.main()
