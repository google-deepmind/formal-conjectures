# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy at https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Offline integrity checks; these do not measure mathematical review quality."""

import copy
import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import review_eval as ev

spec = importlib.util.spec_from_file_location(
    "trigger_eval", ev.HERE / "review-eval/trigger_eval.py"
)
trigger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(trigger)
spec = importlib.util.spec_from_file_location(
    "workspace_server", ev.HERE / "review-eval/workspace_server.py"
)
workspace = importlib.util.module_from_spec(spec)
spec.loader.exec_module(workspace)


class EvalTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.suite_path = (
            Path(__file__).resolve().parents[1]
            / ".agents/skills/formal-conjectures-review/evals/benchmark.json"
        )
        self.suite = ev.load_suite(self.suite_path)

    def test_catalog_has_real_provenance_and_family_disjoint_splits(self):
        self.assertEqual(len(self.suite["cases"]), 24)
        self.assertEqual(len({c["family"] for c in self.suite["cases"]}), 12)
        for c in self.suite["cases"]:
            self.assertRegex(c["provenance"]["source_commit"], r"^[a-f0-9]{40}$")
            self.assertEqual(c["gold"]["status"], "provisional")

    def test_baseline_only_differs_by_optional_skill_instruction(self):
        c = self.suite["cases"][0]
        baseline = ev.prompt(c, {"id": "opaque"}, "baseline", "model")
        skilled = ev.prompt(c, {"id": "opaque"}, "skill", "model")
        self.assertTrue(skilled.startswith(baseline))
        for hidden in ("gold", c["gold"]["defects"][0]["description"], c["provenance"]["source_commit"]):
            self.assertNotIn(hidden, baseline)
        self.assertNotIn("/skill", baseline)
        self.assertNotIn("source-fidelity", baseline)
        self.assertNotIn("NEEDS REVISION", baseline)

    def test_symlinks_and_traversal_are_not_input_files(self):
        (self.root / "file").write_text("x")
        (self.root / "link").symlink_to(self.root / "file")
        for path in ("../file", "/tmp/file", "link"):
            with self.assertRaises(ValueError):
                ev.asset(self.root, path)

    def test_family_cannot_cross_split_even_for_corrected_or_workflow_case(self):
        suite = copy.deepcopy(self.suite)
        suite["cases"][1]["split"] = "qualification"
        ev.write(self.root / "suite.json", suite)
        with self.assertRaisesRegex(ValueError, "family crosses"):
            ev.load_suite(self.root / "suite.json")

    def test_qualification_requires_human_keys_before_docker_or_outputs(self):
        with patch("review_eval.subprocess.check_output") as command:
            with self.assertRaisesRegex(ValueError, "human-adjudicated"):
                ev.freeze(self.suite_path, self.root, self.root / "out", "image", ["R07"], 1, 60, 10)
            command.assert_not_called()
        self.assertFalse((self.root / "out").exists())

    def test_missing_named_human_evidence_cannot_promote_key(self):
        suite = copy.deepcopy(self.suite)
        suite["cases"][0]["gold"]["status"] = "human_adjudicated"
        ev.write(self.root / "suite.json", suite)
        with self.assertRaisesRegex(ValueError, "missing adjudication"):
            ev.load_suite(self.root / "suite.json")

    def test_key_adjudication_packets_do_not_reveal_provisional_labels(self):
        ev.key_packet(self.suite_path, self.root / "keys")
        packet = ev.read(self.root / "keys/R01.json")
        self.assertEqual(set(packet), {"prompt", "candidate", "sources", "prior_context"})
        self.assertNotIn(
            self.suite["cases"][0]["gold"]["defects"][0]["description"], ev.encode(packet).decode()
        )
        forms = ev.read(self.root / "keys/adjudication.json")
        self.assertEqual(len(forms), len(self.suite["cases"]))
        self.assertTrue(all(f["reviewer"] is None and f["defects"] is None for f in forms))

    def assessment(self):
        return {
            "gold_status": "confirmed",
            "detected_defects": ["domain"],
            "findings": [
                {
                    "index": 0,
                    "status": "supported",
                    "actionable": True,
                    "repair": "not_checked",
                    "duplicate": False,
                    "evidence": "Source explicitly discusses k=-1.",
                }
            ],
            "uncertainty": "not_applicable",
            "comments": "Documentary mismatch.",
        }

    def test_assessment_requires_every_finding_and_only_known_defect_ids(self):
        c = self.suite["cases"][0]
        ev.validate_assessment(self.assessment(), c, 1)
        for field, value in [
            ("findings", []),
            ("detected_defects", ["invented"]),
            ("detected_defects", ["domain", "domain"]),
            ("detected_defects", [{}]),
        ]:
            a = self.assessment()
            a[field] = value
            with self.assertRaises(ValueError):
                ev.validate_assessment(a, c, 1)
        a = self.assessment()
        a["findings"][0]["index"] = False
        with self.assertRaises(ValueError):
            ev.validate_assessment(a, c, 1)

    def test_native_grading_schema_bounds_finding_indices_and_count(self):
        findings = ev.assessment_schema(3)["properties"]["findings"]
        self.assertEqual((findings["minItems"], findings["maxItems"]), (3, 3))
        self.assertEqual(findings["items"]["properties"]["index"]["maximum"], 2)

    def test_reconciliation_schema_permits_only_retained_prior_paths(self):
        schema = ev.review_schema({"id": "id", "scope": ["Example.lean"]}, context=["evidence/prior.txt"])
        reference = schema["properties"]["reconciliations"]["items"]["properties"]["prior_evidence"]
        self.assertEqual(reference, {"type": "string", "enum": ["evidence/prior.txt"]})
        fresh = ev.review_schema({"id": "id", "scope": ["Example.lean"]})
        self.assertEqual(fresh["properties"]["reconciliations"]["maxItems"], 0)

    def test_calibration_is_separate_from_source_disclosure(self):
        a = self.assessment() | {
            "uncertainty": "appropriate",
            "verdict_calibration": "inappropriate",
            "verdict_evidence": "An unresolved source reading was escalated to a semantic defect.",
            "rereview_handling": "not_applicable",
            "rereview_evidence": "Fresh review.",
        }
        ev.validate_assessment(a, self.suite["cases"][0], 1)
        del a["verdict_evidence"]
        with self.assertRaises(ValueError):
            ev.validate_assessment(a, self.suite["cases"][0], 1)

    def test_assessment_set_cannot_be_applied_to_different_review_inputs(self):
        self.run_root()
        ev.write(self.root / "grades/config.json", {"review_manifest_sha256": "0" * 64})
        with self.assertRaisesRegex(ValueError, "another review iteration"):
            ev.summarize(self.root, self.root / "grades")

    def run_root(self):
        ev.write(self.root / "suite.json", self.suite)
        manifest = {
            "jobs": [
                {"id": "a", "case": "R01", "family": "479", "arm": "skill", "repeat": 0},
                {"id": "b", "case": "R01", "family": "479", "arm": "baseline", "repeat": 0},
            ],
            "frozen_files": ev.files(self.root),
            "tooling": {
                p.name: ev.sha(p.read_bytes())
                for p in (ev.HERE / name for name in ev.REVIEW_TOOLS)
            },
        }
        ev.write(self.root / "manifest.json", manifest)
        return manifest

    def test_failed_and_unstarted_runs_remain_visible(self):
        self.run_root()
        ev.write(self.root / "runs/a/result.json", {"status": "timeout"})
        s = ev.summarize(self.root)
        self.assertEqual(s["arms"]["skill"]["scheduled"], 1)
        self.assertEqual(s["arms"]["baseline"]["scheduled"], 1)
        self.assertEqual([r["status"] for r in s["runs"]], ["timeout", "not_run"])
        self.assertEqual(s["unique_families"], 1)

    def test_disputed_reference_is_unresolved_not_a_reviewer_failure(self):
        self.run_root()
        ev.write(self.root / "runs/a/model/answer.json", {"findings": [{}]})
        a = self.assessment()
        a["gold_status"] = "disputed"
        a["detected_defects"] = []
        ev.write(self.root / "assessments/a/assessment.json", a)
        s = ev.summarize(self.root)["arms"]["skill"]
        self.assertEqual(s["unresolved_keys"], 1)
        self.assertEqual(s["reference_defects"], 0)
        self.assertEqual(s["unsupported_findings"], 0)
        self.assertEqual(s["supported_findings"], 1)
        self.assertEqual(s["valid_repairs"], 0)

    def test_frozen_source_tampering_is_rejected(self):
        self.run_root()
        (self.root / "suite.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "frozen inputs changed"):
            ev.verify(self.root)

    def test_schema_has_no_reviewer_controlled_verdict(self):
        schema = ev.review_schema({"id": "opaque", "scope": ["FormalConjectures/Example.lean"]})
        self.assertNotIn("verdict", schema["properties"])
        self.assertEqual(
            schema["properties"]["findings"]["items"]["properties"]["file"]["enum"],
            ["FormalConjectures/Example.lean"],
        )

    def test_baseline_procedure_is_an_explicit_control_receipt(self):
        procedure = ev.review_procedure(self.root / "absent-skill", "baseline")
        request = {
            "schema_version": ev.rr.LEGACY_REQUEST_VERSION,
            "repository": "test/repo",
            "head_commit": "a" * 40,
            "merge_base": "b" * 40,
            "scope": ["FormalConjectures/Example.lean"],
            "sources": [],
            "procedure": ev.rr.descriptors(procedure),
            "required_checks": ["build"],
        }
        request["id"] = ev.rr.request_id(request)
        ev.rr.validate_request(request)
        self.assertIn(b"No optional review skill was supplied", procedure["procedure/SKILL.md"])

    def test_native_output_schema_requires_exact_evidence_paths(self):
        schema = ev.review_schema(
            {
                "id": "opaque",
                "scope": ["FormalConjectures/Example.lean"],
                "sources": [{"path": "sources/paper.txt"}],
            },
            2,
        )
        evidence = schema["properties"]["findings"]["items"]["properties"]["evidence"]
        self.assertEqual(
            evidence["items"]["enum"],
            ["sources/paper.txt", "evidence/tool-001.json", "evidence/tool-002.json"],
        )
        self.assertNotIn("sources/paper.txt says this is false", evidence["items"]["enum"])

    def test_routing_queries_have_distinct_validation_examples_and_both_classes(self):
        path = self.suite_path.with_name("triggers.json")
        development = trigger.load_queries(path, "development")
        validation = trigger.load_queries(path, "validation")
        self.assertEqual((len(development), len(validation)), (12, 8))
        self.assertFalse({q["query"] for q in development} & {q["query"] for q in validation})
        for split in (development, validation):
            self.assertEqual({q["should_trigger"] for q in split}, {True, False})

    def test_routing_observes_a_successful_load_not_the_models_claim(self):
        event = {"type": "item.completed", "item": {"type": "agent_message", "text": "I loaded the skill"}}
        self.assertFalse(trigger.loaded_skill([event]))

        event["item"] = {
            "type": "mcp_tool_call",
            "server": "review_workspace",
            "tool": "load_skill",
            "status": "completed",
            "error": None,
            "result": {},
        }
        self.assertTrue(trigger.loaded_skill([event]))
        event["item"]["result"]["is_error"] = True
        self.assertFalse(trigger.loaded_skill([event]))
        event["item"]["result"] = {}
        event["item"]["error"] = "not available"
        self.assertFalse(trigger.loaded_skill([event]))

    def test_host_resource_discovery_must_be_empty(self):
        call = {
            "type": "mcp_tool_call",
            "server": "codex",
            "tool": "list_mcp_resources",
            "result": {"content": [{"type": "text", "text": '{"resources": []}'}]},
        }
        self.assertTrue(ev.allowed_call(call))
        call["result"]["content"][0]["text"] = '{"resources": [{"uri": "host://context"}]}'
        self.assertFalse(ev.allowed_call(call))
        call["result"]["content"][0]["text"] = "unparseable"
        self.assertFalse(ev.allowed_call(call))
        call["tool"] = "read_mcp_resource"
        self.assertFalse(ev.allowed_call(call))

    def test_snapshot_identity_is_deterministic_and_git_metadata_is_not_world_writable(self):
        identities = []
        for name in ("skill", "baseline"):
            repo = self.root / name
            repo.mkdir()
            identities.append(ev.snapshot(repo, "FormalConjectures/Example.lean", b"-- test snapshot\n"))
            self.assertFalse((repo / ".git/config").stat().st_mode & 0o022)
        self.assertEqual(*identities)

    def test_build_status_uses_receipts_instead_of_shell_claims(self):
        binding = {
            "isolation": "fresh_container",
            "image": "sha256:" + "a" * 64,
            "candidate_path": "FormalConjectures/Example.lean",
            "candidate_sha256": "b" * 64,
            "module": "Example",
        }
        evidence = {
            "evidence/tool-001.json": ev.encode(
                {
                    "kind": "command",
                    "exit_code": 0,
                    "stdout": "Build completed successfully",
                    "timed_out": False,
                }
            )
        }
        self.assertEqual(ev.build_checks(evidence, "Example", binding), [])
        for code, expected in (
            (0, "pass"),
            (1, "fail"),
            (124, "error"),
            (None, "error"),
        ):
            evidence["evidence/tool-002.json"] = ev.encode(
                {
                    "kind": "build",
                    "exit_code": code,
                    "timed_out": False,
                    "environment": binding,
                    "command": [
                        "timeout",
                        "-k",
                        "2",
                        "60",
                        "lake",
                        "--wfail",
                        "build",
                        "Example",
                    ],
                }
            )
            check = ev.build_checks(evidence, "Example", binding)[0]
            self.assertEqual(check["status"], expected)
            self.assertEqual(check["evidence"], ["evidence/tool-002.json"])

        for field, value in (
            ("environment", None),
            ("environment", binding | {"image": "other"}),
            ("environment", binding | {"candidate_sha256": "c" * 64}),
            ("command", ["sh", "-c", "true"]),
        ):
            receipt = ev.rr.parse(evidence["evidence/tool-002.json"])
            receipt[field] = value
            with self.assertRaisesRegex(ValueError, "does not match request"):
                ev.build_checks({"evidence/tool-002.json": ev.encode(receipt)}, "Example", binding)

    def workspace_tools(self):
        candidate = self.root / "candidate.lean"
        candidate.write_text("example : True := True.intro\n")
        (self.root / "evidence").mkdir()
        return workspace.WorkspaceTools(
            "scratch",
            self.root,
            "FormalConjectures.Example",
            30,
            "sha256:" + "a" * 64,
            candidate,
            "FormalConjectures/Example.lean",
        )

    def test_build_never_reuses_scratch_container_or_mounts(self):
        tools = self.workspace_tools()
        with patch.object(
            workspace.subprocess,
            "run",
            return_value=subprocess.CompletedProcess([], 0, b"built", b""),
        ) as run:
            receipt = tools.build()
        command = run.call_args_list[0].args[0]
        self.assertEqual(command[:3], ["docker", "run", "--rm"])
        self.assertIn("--network=none", command)
        self.assertEqual(
            [arg for arg in command if arg.startswith("--mount=")],
            [
                f"--mount=type=bind,src={tools.candidate},dst=/workspace/FormalConjectures/Example.lean,readonly"
            ],
        )
        self.assertEqual(receipt["environment"], tools.binding)
        self.assertEqual(run.call_args_list[-1].args[0], ["docker", "rm", "-f", "scratch-build"])

    def test_build_timeout_removes_container_and_records_error(self):
        tools = self.workspace_tools()
        with patch.object(
            workspace.subprocess,
            "run",
            side_effect=[
                subprocess.TimeoutExpired("docker", 65),
                subprocess.CompletedProcess([], 0),
            ],
        ) as run:
            receipt = tools.build()
        self.assertTrue(receipt["timed_out"])
        self.assertEqual(run.call_args_list[-1].args[0], ["docker", "rm", "-f", "scratch-build"])
        check = ev.build_checks(
            {receipt["evidence"]: ev.encode(receipt)}, tools.module, tools.binding
        )
        self.assertEqual(check[0]["status"], "error")

    def test_changed_candidate_is_rejected_before_build(self):
        tools = self.workspace_tools()
        tools.candidate.write_text("-- replaced\n")
        with (
            patch.object(workspace.subprocess, "run") as run,
            self.assertRaisesRegex(ValueError, "Candidate changed"),
        ):
            tools.build()
        run.assert_not_called()

    def test_missing_inputs_leave_a_failure_record_before_model_startup(self):
        manifest = self.run_root()
        with patch("review_eval.invoke_model") as model, patch("review_eval.subprocess.run"):
            ev.run_one(self.root, manifest, manifest["jobs"][0], "gpt-5.6-sol")
        model.assert_not_called()
        result = ev.read(self.root / "runs/a/result.json")
        self.assertEqual(result["status"], "environment_error")
        self.assertEqual(result["report_status"], "invalid")


if __name__ == "__main__":
    unittest.main()
