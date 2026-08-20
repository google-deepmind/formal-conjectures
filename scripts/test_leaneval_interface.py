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

"""Tests for the importer-to-generator interface.

The two values here are the whole contract between the half of this work
Formal Conjectures owns and the half `leanprover/lean-eval-generator` will
own. A value that does not survive being written out and read back is not a
contract, and a manifest that has lost the source commit cannot be regenerated
when Formal Conjectures corrects the statement upstream.
"""

import unittest

from leaneval_interface import (
    DefinitionHole,
    MarkedUpModule,
    ProblemManifest,
    SourceRecord,
    TargetRecord,
    slug,
)


def a_source(**overrides):
    fields = {
        "repository": "https://github.com/google-deepmind/formal-conjectures",
        "commit": "a" * 40,
        "path": "FormalConjectures/Example.lean",
        "blob_sha": "b" * 40,
        "module": "FormalConjectures.Example",
        "declaration": "erdos_940",
        "copied_dependencies": ("Foo.bar",),
        "original_declaration": "theorem erdos_940 : True := by\n  sorry",
        "lean_toolchain": "leanprover/lean4:v4.27.0",
        "mathlib_revision": "c" * 40,
    }
    fields.update(overrides)
    return SourceRecord(**fields)


def a_target(**overrides):
    fields = {
        "repository": "leanprover/lean-eval",
        "commit": "e" * 40,
        "lean_toolchain": "leanprover/lean4:v4.33.0",
        "mathlib_revision": "f" * 40,
        "comparator": "d" * 40,
        "lean4export": "0" * 40,
    }
    fields.update(overrides)
    return TargetRecord(**fields)


def a_manifest(**overrides):
    fields = {
        "id": "erdos_940",
        "theorem": "erdos_940",
        "qualified_theorem": "Erdos.erdos_940",
        "apply_arguments": ("n",),
        "holes": (DefinitionHole(name="erdos_940_answer", type="ENNReal"),),
        "permitted_axioms": ("propext", "Quot.sound", "Classical.choice"),
        "source": a_source(),
        "source_url": "https://www.erdosproblems.com/940",
    }
    fields.update(overrides)
    return ProblemManifest(**fields)


A_MODULE = MarkedUpModule(
    dependencies="def Foo.bar := 1",
    scope="open Erdos",
    holes="noncomputable def erdos_940_answer : ENNReal := sorry",
    statement="theorem erdos_940 : erdos_940_answer = 0 := by\n  sorry",
)


class ManifestTest(unittest.TestCase):
    def test_source_commit_and_declaration_are_required(self):
        # lean-eval#536 names both, and neither is something the generator can
        # supply: it sees a Lean module, not a repository.
        with self.assertRaisesRegex(SystemExit, "no FC source commit"):
            a_manifest(source=a_source(commit=""))
        with self.assertRaisesRegex(SystemExit, "no FC declaration id"):
            a_manifest(source=a_source(declaration=""))

    def test_the_manifest_does_not_carry_the_consumers_pins(self):
        # lean-eval#536 gives LeanEval the pin regime. A manifest asserting it
        # would go stale when LeanEval bumped, with nothing here to notice.
        self.assertNotIn("target", a_manifest().to_json_object())

    def test_the_pins_the_hole_types_were_read_at_are_recorded(self):
        # The consumer supplies its own pins, but it cannot know where these
        # hole types were read unless the manifest says so.
        payload = a_manifest().to_json_object()
        self.assertEqual(payload["source"]["lean_toolchain"], "leanprover/lean4:v4.27.0")

    def test_the_manifest_survives_a_round_trip(self):
        manifest = a_manifest()
        self.assertEqual(ProblemManifest.from_json(manifest.to_json()), manifest)

    def test_the_serialised_manifest_carries_the_commit_and_declaration(self):
        # A reviewer of a generated workspace reads this file, so the two
        # fields have to be in it under their own names.
        payload = a_manifest().to_json_object()
        self.assertEqual(payload["source"]["commit"], "a" * 40)
        self.assertEqual(payload["source"]["declaration"], "erdos_940")

    def test_a_manifest_from_another_schema_version_is_refused(self):
        payload = a_manifest().to_json_object()
        payload["schema_version"] = 99
        with self.assertRaises(SystemExit):
            ProblemManifest.from_json_object(payload)

    def test_hole_declaration_is_the_text_the_module_carries(self):
        hole = DefinitionHole(name="t_answer", type="Prop")
        self.assertEqual(
            hole.declaration(), "noncomputable def t_answer : Prop := sorry"
        )


class MarkedUpModuleTest(unittest.TestCase):
    def test_the_module_stands_on_mathlib_alone(self):
        self.assertTrue(A_MODULE.render().startswith("import Mathlib\n"))

    def test_the_module_survives_a_round_trip(self):
        self.assertEqual(MarkedUpModule.parse(A_MODULE.render()), A_MODULE)

    def test_an_empty_region_still_round_trips(self):
        # Most statements have no answer slot, so the holes region is empty
        # and the generator must still find it.
        module = MarkedUpModule(
            dependencies="def f := 1", scope="", holes="", statement="theorem t : True"
        )
        self.assertEqual(MarkedUpModule.parse(module.render()), module)

    def test_a_missing_region_is_refused(self):
        text = A_MODULE.render().replace("-- @region holes\n", "")
        with self.assertRaisesRegex(SystemExit, "`holes` region"):
            MarkedUpModule.parse(text)

    def test_an_unknown_region_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "unknown region"):
            MarkedUpModule.parse("import Mathlib\n\n-- @region proof\n")

    def test_a_repeated_region_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "appears twice"):
            MarkedUpModule.parse(A_MODULE.render() + "\n-- @region scope\n")

    def test_a_copied_declaration_that_looks_like_a_marker_is_refused(self):
        # It would split the module somewhere the importer did not choose,
        # and the generator would have no way to notice.
        module = MarkedUpModule(
            dependencies="-- @region statement\ndef f := 1",
            scope="",
            holes="",
            statement="theorem t : True",
        )
        with self.assertRaisesRegex(SystemExit, "contains a region marker"):
            module.render()

    def test_regions_out_of_order_are_refused(self):
        # The order is what makes the module elaborate: a hole is used by the
        # statement below it, and both need the scope above them.
        module = MarkedUpModule.parse(A_MODULE.render())
        reordered = (
            "import Mathlib\n"
            f"\n-- @region scope\n{module.scope}\n"
            f"\n-- @region dependencies\n{module.dependencies}\n"
            f"\n-- @region holes\n{module.holes}\n"
            f"\n-- @region statement\n{module.statement}\n"
        )
        with self.assertRaisesRegex(SystemExit, "out of order"):
            MarkedUpModule.parse(reordered)


class SlugTest(unittest.TestCase):
    def test_a_qualified_declaration_becomes_an_identifier(self):
        # A Lake package name is an identifier, so the dots cannot survive.
        self.assertEqual(
            slug("erdos_940.variants.large_integers"),
            "erdos_940_variants_large_integers",
        )


if __name__ == "__main__":
    unittest.main()
