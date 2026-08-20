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
    _utf16_column,
    build_problem,
    build_request,
    declaration_spans,
    module_declarations,
    parse_response,
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
        "apply_arguments": (),
        "holes": (DefinitionHole(name="erdos_940_answer", type="ENNReal"),),
        "permitted_axioms": ("propext", "Quot.sound", "Classical.choice"),
        "source": a_source(),
        "source_url": "https://www.erdosproblems.com/940",
        "category": "research open",
    }
    fields.update(overrides)
    return ProblemManifest(**fields)


A_MODULE = MarkedUpModule(
    dependencies="def Foo.bar := 1",
    scope="open Erdos",
    holes="noncomputable def erdos_940_answer : ENNReal := sorry",
    statement="theorem erdos_940 : erdos_940_answer = 0 := by\n  sorry",
    dependency_declarations=(("Foo.bar", "def Foo.bar := 1"),),
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

    def test_the_module_carries_no_markers(self):
        # The handed-over module is plain Lean: `@[eval_problem]` does not
        # exist outside lean-eval, and the request's resolved holes already
        # say where the declarations are.
        rendered = A_MODULE.render()
        self.assertNotIn("@[eval_problem]", rendered)
        self.assertNotIn("-- @region", rendered)

    def test_regions_render_in_declaration_order(self):
        # A hole is used by the statement below it, and both need the scope
        # above them.
        rendered = A_MODULE.render()
        positions = [
            rendered.index(getattr(A_MODULE, region))
            for region in ("dependencies", "scope", "holes", "statement")
        ]
        self.assertEqual(positions, sorted(positions))

    def test_an_empty_region_leaves_no_blank_gap(self):
        module = MarkedUpModule(
            dependencies="def f := 1", scope="", holes="", statement="theorem t : True"
        )
        self.assertEqual(
            module.render(),
            "import Mathlib\n\ndef f := 1\n\ntheorem t : True\n",
        )


class SlugTest(unittest.TestCase):
    def test_a_qualified_declaration_becomes_an_identifier(self):
        # A Lake package name is an identifier, so the dots cannot survive.
        self.assertEqual(
            slug("erdos_940.variants.large_integers"),
            "erdos_940_variants_large_integers",
        )


if __name__ == "__main__":
    unittest.main()


class DeclarationSpanTest(unittest.TestCase):
    """Spans are computed from the rendered text, exactly."""

    def test_every_declaration_gets_the_span_of_its_own_text(self):
        text = A_MODULE.render()
        spans = declaration_spans(text, module_declarations(A_MODULE, a_manifest()))
        lines = text.split("\n")
        for span in spans:
            with self.subTest(name=span["name"]):
                sliced = "\n".join(
                    lines[span["startLine"] - 1 : span["endLine"]]
                )[span["startColumn"] :]
                self.assertTrue(sliced.startswith(("def", "noncomputable", "theorem")))

    def test_a_body_appearing_twice_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "more than once"):
            declaration_spans(
                "def f := 1\ndef f := 1\n", [("f", "def f := 1", "def", None)]
            )

    def test_a_missing_body_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "not found"):
            declaration_spans("def g := 1\n", [("f", "def f := 1", "def", None)])

    def test_utf16_columns_count_supplementary_plane_pairs(self):
        # 𝕜 is beyond the BMP: one codepoint, two UTF-16 units. An `.ilean`
        # column after it disagrees with the codepoint column by one.
        text = "def 𝕜x := 1\ntheorem t : True := trivial\n"
        (span,) = declaration_spans(
            text, [("t", "theorem t : True := trivial", "theorem", None)]
        )
        self.assertEqual(span["startColumn"], span["utf16StartColumn"])
        line = "abc𝕜 def f := 1"
        self.assertEqual(_utf16_column(line, 5), 6)


class BuildProblemTest(unittest.TestCase):
    def test_the_problem_satisfies_the_contract_shape(self):
        problem, ilean = build_problem(A_MODULE, a_manifest())
        self.assertEqual(problem["id"], "erdos_940")
        self.assertEqual(problem["group"], "open-conjectures")
        self.assertEqual(problem["moduleName"], "erdos_940")
        self.assertEqual(
            problem["holes"], ["erdos_940_answer", "erdos_940"]
        )
        self.assertEqual(problem["moduleContent"], A_MODULE.render())
        kinds = [hole["kind"] for hole in problem["resolvedHoles"]]
        self.assertEqual(kinds, ["def", "theorem"])
        # Helpers are `.ilean` material, not holes.
        self.assertIn("Foo.bar", ilean)
        self.assertNotIn(
            "Foo.bar", [hole["declarationName"] for hole in problem["resolvedHoles"]]
        )

    def test_the_theorem_hole_carries_the_copied_dependencies(self):
        problem, _ = build_problem(A_MODULE, a_manifest())
        theorem = problem["resolvedHoles"][-1]
        self.assertEqual(theorem["sameModuleDependencies"], ["Foo.bar"])
        self.assertEqual(problem["resolvedHoles"][0]["sameModuleDependencies"], [])

    def test_a_non_problem_category_is_refused(self):
        with self.assertRaises(SystemExit):
            build_problem(A_MODULE, a_manifest(category="API"))

    def test_the_category_rides_along_as_a_tag(self):
        problem, _ = build_problem(A_MODULE, a_manifest(category="research solved"))
        self.assertIn("research-solved", problem["tags"])

    def test_a_set_override_keeps_a_solved_member_in_its_set(self):
        # The frozen list is immutable while its members keep getting
        # solved, so the set decides the tab and the tag says which are
        # solved (formal-conjectures#5075).
        problem, _ = build_problem(
            A_MODULE,
            a_manifest(category="research solved"),
            group="open-conjectures",
        )
        self.assertEqual(problem["group"], "open-conjectures")

    def test_a_set_override_does_not_admit_a_non_problem(self):
        with self.assertRaises(SystemExit):
            build_problem(
                A_MODULE, a_manifest(category="API"), group="open-conjectures"
            )


class BuildRequestTest(unittest.TestCase):
    def test_the_request_carries_the_targets_pins(self):
        problem, _ = build_problem(A_MODULE, a_manifest())
        request = build_request([problem], a_target(), "-- test", "context")
        self.assertEqual(request["schemaVersion"], 1)
        self.assertEqual(request["leanToolchain"], "leanprover/lean4:v4.33.0")
        self.assertEqual(request["mathlib"]["rev"], "f" * 40)
        self.assertEqual(request["templates"]["workspaceTest"], "-- test")

    def test_duplicate_ids_are_refused(self):
        problem, _ = build_problem(A_MODULE, a_manifest())
        with self.assertRaisesRegex(SystemExit, "duplicate workspace id"):
            build_request([problem, problem], a_target(), "", "context")


class ParseResponseTest(unittest.TestCase):
    def _response(self, content="hello"):
        import hashlib
        import json

        return json.dumps(
            {
                "schemaVersion": 1,
                "files": [
                    {
                        "problemId": "p",
                        "path": "a.txt",
                        "sha256": hashlib.sha256(content.encode()).hexdigest(),
                        "content": "hello",
                    }
                ],
            }
        )

    def test_a_good_response_yields_the_file_map(self):
        self.assertEqual(parse_response(self._response()), {"p": {"a.txt": "hello"}})

    def test_a_damaged_digest_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "does not match"):
            parse_response(self._response(content="tampered"))

    def test_an_unknown_schema_version_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "schema version"):
            parse_response('{"schemaVersion": 2, "files": []}')
