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
from unittest import mock

from leaneval_interface import (
    DefinitionHole,
    MarkedUpModule,
    ProblemManifest,
    ProducerRecord,
    SourceRecord,
    TargetRecord,
    _utf16_column,
    build_problem,
    build_request,
    declaration_spans,
    module_declarations,
    parse_response,
    problem_group,
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
        "copied_dependencies": (
            {
                "declaration": "Foo.bar",
                "module": "FormalConjectures.Example",
                "path": "FormalConjectures/Example.lean",
                "range": {"startLine": 3, "startColumn": 0, "endLine": 4, "endColumn": 11},
                "content_sha256": "d" * 64,
            },
        ),
        "original_range": {"startLine": 20, "startColumn": 0, "endLine": 22, "endColumn": 7},
        "original_sha256": "e" * 64,
        "lean_toolchain": "leanprover/lean4:v4.33.1",
        "mathlib_revision": "c" * 40,
    }
    fields.update(overrides)
    return SourceRecord(**fields)


def a_target(**overrides):
    fields = {
        "lean_toolchain": "leanprover/lean4:v4.33.0",
        "mathlib_revision": "f" * 40,
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
        self.assertEqual(payload["source"]["lean_toolchain"], "leanprover/lean4:v4.33.1")

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
    def _response(self, content="hello", **entry_overrides):
        import hashlib
        import json

        entry = {
            "problemId": "p",
            "path": "a.txt",
            "sha256": hashlib.sha256(content.encode()).hexdigest(),
            "content": "hello",
        }
        entry.update(entry_overrides)
        return json.dumps({"schemaVersion": 1, "files": [entry]})

    def test_a_traversal_path_is_refused(self):
        for path in ("../outside.txt", "a/../../b.txt", "/etc/x", "a//b.txt",
                     "./a.txt", "a\\b.txt", "C:whatever"):
            with self.subTest(path=path):
                with self.assertRaisesRegex(SystemExit, "response path"):
                    parse_response(self._response(path=path))

    def test_the_sidecar_name_is_refused(self):
        # A response naming fc-provenance.json would silently lose to the
        # sidecar written after it — and its recorded digest would then
        # describe bytes no longer on disk.
        with self.assertRaisesRegex(SystemExit, "provenance sidecar"):
            parse_response(self._response(path="fc-provenance.json"))

    def test_unknown_response_keys_are_refused(self):
        import json

        payload = json.loads(self._response())
        payload["extra"] = True
        with self.assertRaisesRegex(SystemExit, "unknown keys"):
            parse_response(json.dumps(payload))

    def test_unknown_entry_keys_are_refused(self):
        with self.assertRaisesRegex(SystemExit, "unknown keys"):
            parse_response(self._response(mode="0755"))

    def test_a_missing_entry_field_is_a_refusal_not_a_crash(self):
        import json

        payload = json.loads(self._response())
        del payload["files"][0]["sha256"]
        with self.assertRaisesRegex(SystemExit, "has no sha256"):
            parse_response(json.dumps(payload))

    def test_non_json_is_a_refusal_not_a_crash(self):
        with self.assertRaisesRegex(SystemExit, "not JSON"):
            parse_response("lake build output\n{")

    def test_the_returned_workspaces_must_be_the_requested_ones(self):
        with self.assertRaisesRegex(SystemExit, "returned no files for q"):
            parse_response(self._response(), expected_ids=["p", "q"])
        with self.assertRaisesRegex(SystemExit, "nothing requested"):
            parse_response(self._response(), expected_ids=[])

    def test_a_good_response_yields_the_file_map(self):
        self.assertEqual(parse_response(self._response()), {"p": {"a.txt": "hello"}})

    def test_a_damaged_digest_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "does not match"):
            parse_response(self._response(content="tampered"))

    def test_an_unknown_schema_version_is_refused(self):
        with self.assertRaisesRegex(SystemExit, "schema version"):
            parse_response('{"schemaVersion": 2, "files": []}')


class ProvenanceSidecarTest(unittest.TestCase):
    """The sidecar is the schema-version-1 provenance boundary: strict, deterministic, digested."""

    def test_digests_round_trip(self):
        bound = a_manifest().with_digests("a" * 64, {"Challenge.lean": "b" * 64, "A.lean": "c" * 64})
        again = ProblemManifest.from_json(bound.to_json())
        self.assertEqual(again.module_sha256, "a" * 64)
        self.assertEqual(dict(again.file_sha256), {"A.lean": "c" * 64, "Challenge.lean": "b" * 64})

    def test_serialisation_is_key_sorted(self):
        text = a_manifest().with_digests("a" * 64, {"b": "1" * 64, "a": "2" * 64}).to_json()
        keys = [line.split('"')[1] for line in text.splitlines() if line.startswith('  "')]
        self.assertEqual(keys, sorted(keys))

    def test_unknown_keys_are_refused(self):
        payload = a_manifest().to_json_object()
        payload["notes"] = "anything"
        with self.assertRaises(SystemExit):
            ProblemManifest.from_json_object(payload)

    def test_unknown_digest_keys_are_refused(self):
        payload = a_manifest().with_digests("a" * 64, {}).to_json_object()
        payload["digests"]["blake3"] = "d" * 64
        with self.assertRaises(SystemExit):
            ProblemManifest.from_json_object(payload)

    def test_the_request_digest_survives_a_round_trip(self):
        bound = a_manifest().with_digests("a" * 64, {}, request_sha256="d" * 64)
        loaded = ProblemManifest.from_json(bound.to_json())
        self.assertEqual(loaded.request_sha256, "d" * 64)


class ProblemGroupTest(unittest.TestCase):
    """Categories map to lean-eval groups; non-problems are refused."""

    def _manifest(self, category):
        manifest = mock.Mock()
        manifest.category = category
        manifest.id = "some_problem"
        return manifest

    def test_open_research_is_an_open_conjecture(self):
        self.assertEqual(
            problem_group(self._manifest("research open")),
            "open-conjectures",
        )

    def test_settled_statements_are_evaluation_material(self):
        for category in ("research solved", "textbook", "test"):
            with self.subTest(category=category):
                self.assertEqual(
                    problem_group(self._manifest(category)),
                    "formalization-evaluation",
                )

    def test_api_and_untagged_declarations_are_refused(self):
        for category in ("API", ""):
            with self.subTest(category=category):
                with self.assertRaises(SystemExit):
                    problem_group(self._manifest(category))


class StatementPrefixSpanTest(unittest.TestCase):
    def test_the_span_starts_at_the_declaration_keyword(self):
        from leaneval_interface import module_declarations

        module = MarkedUpModule(
            dependencies="def Foo.bar := 1",
            scope="",
            holes="",
            statement="open scoped Classical in\ntheorem t : True := by\n  sorry",
            dependency_declarations=(("Foo.bar", "def Foo.bar := 1"),),
        )
        manifest = a_manifest(
            theorem="t", qualified_theorem="t", holes=(), apply_arguments=()
        )
        *_, statement_entry = module_declarations(module, manifest)
        self.assertTrue(statement_entry[1].startswith("theorem t"))
        self.assertNotIn("Classical in", statement_entry[1])

def a_producer(**overrides):
    fields = {
        "importer_commit": "9" * 40,
        "importer_dirty": False,
        "generator_repository": "https://github.com/leanprover/lean-eval-generator",
        "generator_rev": "7" * 40,
        "contract_version": 1,
        "target_lean_toolchain": "leanprover/lean4:v4.33.0",
        "target_mathlib_revision": "6" * 40,
        "target_comparator": "c" * 40,
        "target_lean4export": "1" * 40,
    }
    fields.update(overrides)
    return ProducerRecord(**fields)


class ProducerRecordTest(unittest.TestCase):
    """The sidecar names what produced the artifact, and only that."""

    def test_the_producer_survives_a_round_trip(self):
        bound = a_manifest().with_producer(a_producer(importer_dirty=True))
        loaded = ProblemManifest.from_json(bound.to_json())
        self.assertEqual(loaded.producer, bound.producer)
        self.assertTrue(loaded.producer.importer_dirty)

    def test_a_manifest_without_a_producer_stays_without_one(self):
        loaded = ProblemManifest.from_json(a_manifest().to_json())
        self.assertIsNone(loaded.producer)

    def test_unknown_producer_keys_are_refused(self):
        payload = a_manifest().with_producer(a_producer()).to_json_object()
        payload["producer"]["generator"]["binary_path"] = "/tmp/gen"
        with self.assertRaisesRegex(SystemExit, "unknown keys"):
            ProblemManifest.from_json_object(payload)

    def test_unknown_copied_dependency_keys_are_refused(self):
        payload = a_manifest().to_json_object()
        payload["source"]["copied_dependencies"][0]["blob"] = "f" * 40
        with self.assertRaisesRegex(SystemExit, "unknown keys"):
            ProblemManifest.from_json_object(payload)


if __name__ == "__main__":
    unittest.main()
