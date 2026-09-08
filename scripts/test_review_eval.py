# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy at https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Offline evaluation integrity checks. These do not measure model quality."""

from pathlib import Path
import tempfile
import unittest

import review_eval as ev


class EvalTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def test_packet_prompt_separates_procedure_from_common_task(self):
        packet = {"task": "Review this statement", "artifacts": {"sources/paper": "source bytes"}}
        baseline = ev.prompt(packet, "")
        skilled = ev.prompt(packet, "PROCEDURE SENTINEL")
        self.assertNotIn("PROCEDURE SENTINEL", baseline)
        self.assertIn("PROCEDURE SENTINEL", skilled)
        self.assertEqual(baseline.split("Evidence packet:\n")[1], skilled.split("Evidence packet:\n")[1])

    def test_native_output_contract_uses_repository_paths_for_findings(self):
        packet = {"request": {"id": "request", "scope": ["FormalConjectures/Example.lean"]},
                  "reviewer": "model", "context_policy": "fresh", "prior_reviews": [],
                  "artifacts": {"evidence/candidate.lean": "source"}}
        schema = ev.review_schema(packet)
        finding = schema["properties"]["findings"]["items"]
        self.assertEqual(finding["properties"]["file"]["enum"], ["FormalConjectures/Example.lean"])
        self.assertNotIn("verdict", schema["properties"])
        self.assertFalse(schema["additionalProperties"])

    def test_suite_rejects_paths_before_creating_case_checkouts(self):
        for case_id, path in (("../escape", "Example.lean"), ("01", "/tmp/escape.lean"),
                              ("01", "../escape.lean")):
            ev.write(self.root / "suite.json", {"schema_version": "fc.review-eval.suite.v1",
                     "assets": {}, "cases": [{"id": case_id, "path": path, "files": {},
                                               "context_policy": "fresh"}]})
            with self.assertRaises(ValueError):
                ev.load_suite(self.root / "suite.json")

    def test_json_rejects_duplicate_keys_and_nonfinite_values(self):
        for raw in ('{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
            with self.assertRaises(ValueError):
                ev.parse(raw)

    def test_asset_paths_cannot_escape_or_follow_symlinks(self):
        (self.root / "actual").write_text("data")
        (self.root / "link").symlink_to(self.root / "actual")
        for name in ("../actual", "/actual", "link"):
            with self.assertRaises(ValueError):
                ev.asset(self.root, name)

    def test_all_shipped_assets_are_frozen(self):
        path = Path(__file__).resolve().parents[1] / ".agents/skills/formal-conjectures-review/evals/evals.json"
        suite = ev.load_suite(path)
        for case in suite["cases"]:
            ids = [c["id"] for c in case["gold"]["criteria"]]
            self.assertEqual(len(ids), len(set(ids)))

    def grade(self):
        return {"criteria": [{"id": "c1", "met": True, "reason": "Matches the primary source."}],
                "findings": [{"index": 0, "supported": True, "actionable": True,
                              "duplicate": False, "reason": "Fixes the documented bound."}],
                "contradictory_fixes": False, "disputed_gold": False, "rationale": "Source-backed."}

    def test_grades_require_every_criterion_and_finding_exactly_once(self):
        ev.validate_grade(self.grade(), ["c1"], 1)
        for field in ("criteria", "findings"):
            grade = self.grade()
            grade[field] = []
            with self.assertRaises(ValueError):
                ev.validate_grade(grade, ["c1"], 1)
            grade = self.grade()
            grade[field] *= 2
            with self.assertRaises(ValueError):
                ev.validate_grade(grade, ["c1"], 1)

    def test_grade_flags_cannot_be_strings_or_boolean_indices(self):
        grade = self.grade()
        grade["criteria"][0]["met"] = "true"
        with self.assertRaises(ValueError):
            ev.validate_grade(grade, ["c1"], 1)
        grade = self.grade()
        grade["findings"][0]["index"] = False
        with self.assertRaises(ValueError):
            ev.validate_grade(grade, ["c1"], 1)

    def manifest(self):
        (self.root / "input.txt").write_text("frozen")
        manifest = {"harness_sha256": ev.sha(Path(ev.__file__).read_bytes()),
                    "frozen_files": {"input.txt": ev.sha(b"frozen")}, "suite_sha256": "test-suite",
                    "jobs": [{"id": "a", "case": "01", "arm": "skill", "repeat": 0},
                             {"id": "b", "case": "01", "arm": "baseline", "repeat": 0}]}
        ev.write(self.root / "private-manifest.json", manifest)
        return manifest

    def test_tampered_inputs_stop_comparison(self):
        self.manifest()
        ev.verify_frozen(self.root)
        (self.root / "input.txt").write_text("changed")
        with self.assertRaises(ValueError):
            ev.verify_frozen(self.root)

    def test_missing_and_failed_runs_stay_in_the_denominator(self):
        self.manifest()
        folder = self.root / "runs/b"
        folder.mkdir(parents=True)
        ev.write(folder / "result.json", {"status": "timeout"})
        result = ev.summarize(self.root)
        for arm in result["arms"].values():
            self.assertEqual(arm["scheduled"], 1)
            self.assertEqual(arm["all_criteria_met"], 0)
        self.assertEqual([r["status"] for r in result["runs"]], ["not_run", "timeout"])

    def test_extra_supported_findings_are_not_automatically_noise(self):
        self.manifest()
        folder = self.root / "judgements/a"
        folder.mkdir(parents=True)
        grade = self.grade()
        grade["disputed_gold"] = True
        ev.write(folder / "grade.json", grade)
        totals = ev.summarize(self.root)["arms"]["skill"]
        self.assertEqual(totals["findings"], 1)
        self.assertEqual(totals["unsupported"], 0)
        self.assertEqual(totals["disputed_gold"], 1)
        self.assertEqual(totals["all_criteria_met"], 0)


if __name__ == "__main__":
    unittest.main()
