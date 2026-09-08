#!/usr/bin/env python3
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

"""Offline review-report contract checks; no Lean, model or GitHub calls."""

import copy
from pathlib import Path
import subprocess
import tempfile
import unittest

import review_report as rr


class ReportTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.request_dir = self.root / "request"
        self.evidence_dir = self.root / "checks"
        self.evidence_dir.mkdir()
        self.review_path = self.root / "review.json"
        self.inputs = {"procedure/SKILL.md": b"review procedure\n",
                       "sources/paper.txt": b"Source: for every positive n.\n"}
        self.request = {
            "schema_version": rr.REQUEST_VERSION, "repository": "owner/repo",
            "head_commit": "a" * 40, "merge_base": "b" * 40,
            "scope": ["FormalConjectures/Example.lean"],
            "procedure": rr.descriptors({k: v for k, v in self.inputs.items() if k.startswith("procedure/")}),
            "sources": rr.descriptors({k: v for k, v in self.inputs.items() if k.startswith("sources/")}),
            "required_checks": ["build"],
        }
        self.request["id"] = rr.request_id(self.request)
        rr.write_directory(self.request_dir, self.inputs | {"request.json": rr.encode(self.request)})
        self.review = {"request_id": self.request["id"], "reviewer": "Test reviewer",
                       "context_policy": "fresh", "prior_reviews": [],
                       "coverage": {a: "complete" for a in rr.ANGLES},
                       "findings": [], "questions": []}
        (self.evidence_dir / "evidence").mkdir()
        self.raw = b'{"example":"supplied check receipt; not a real Lean run"}\n'
        (self.evidence_dir / "evidence/build.json").write_bytes(self.raw)
        self.manifest = {"request_id": self.request["id"],
                         "artifacts": [{"path": "evidence/build.json", "sha256": rr.digest(self.raw)}],
                         "checks": [{"kind": "build", "status": "pass", "producer": "test fixture",
                                     "policy": "example build policy", "detail": "Fixture only.",
                                     "evidence": ["evidence/build.json"]}]}

    def run_report(self, current=None):
        self.review_path.write_bytes(rr.encode(self.review))
        (self.evidence_dir / "checks.json").write_bytes(rr.encode(self.manifest))
        return rr.assemble(self.request_dir, current or self.request_dir,
                           self.review_path, self.evidence_dir)

    def report(self):
        return rr.parse(self.run_report()["report.json"])

    def finding(self, **changes):
        return {"angle": "source-fidelity", "file": self.request["scope"][0],
                "line": 7, "severity": "semantic", "message": "A direct source mismatch.",
                "suggestion": "Match the cited bound.", "evidence": ["sources/paper.txt"], **changes}

    def test_complete_advisory_report_is_deterministic(self):
        first, second = self.run_report(), self.run_report()
        self.assertEqual(first, second)
        report = rr.parse(first["report.json"])
        self.assertEqual(report["semantic_verdict"], "CLEAN")
        self.assertEqual(report["authority_effect"], "none")
        self.assertEqual(rr.parse(first["observation.json"])["report_sha256"], rr.digest(first["report.json"]))
        self.assertIn("not independently authenticated", first["summary.md"].decode())

    def test_missing_required_check_is_not_a_pass(self):
        self.manifest["checks"] = []
        report = self.report()
        self.assertEqual(report["checks"][0]["status"], "not_run")
        self.assertEqual(report["semantic_verdict"], "INCOMPLETE")

    def test_fail_and_error_do_not_become_semantic_findings(self):
        for status in ("fail", "error", "not_run"):
            with self.subTest(status=status):
                self.manifest["checks"][0]["status"] = status
                report = self.report()
                self.assertEqual(report["semantic_verdict"], "INCOMPLETE")
                self.assertEqual(report["checks"][0]["status"], status)
                self.assertEqual(report["review"]["findings"], [])

    def test_confirmed_defect_survives_incomplete_coverage(self):
        self.review["findings"] = [self.finding()]
        self.review["coverage"]["statement-soundness"] = "incomplete"
        report = self.report()
        self.assertEqual(report["semantic_verdict"], "NEEDS REVISION")
        self.assertEqual(report["completeness"], "incomplete")

    def test_nit_and_question_precedence(self):
        self.review["findings"] = [self.finding(severity="nit")]
        self.assertEqual(self.report()["semantic_verdict"], "ACCEPT WITH NITS")
        self.review["questions"] = ["Which version of the source is intended?"]
        self.assertEqual(self.report()["semantic_verdict"], "INCOMPLETE")

    def reconciliation(self):
        self.review.update(context_policy="rereview", prior_reviews=["evidence/build.json"])
        return {"prior_evidence": "evidence/build.json", "status": "withdrawn",
                "reason": "The prior claim was contradicted by the retained source.",
                "evidence": ["sources/paper.txt"]}

    def test_withdrawn_finding_is_traceable_without_becoming_a_current_finding(self):
        self.review["reconciliations"] = [self.reconciliation()]
        files = self.run_report()
        report = rr.parse(files["report.json"])
        self.assertEqual(report["semantic_verdict"], "CLEAN")
        self.assertEqual(report["review"]["findings"], [])
        self.assertIn("**withdrawn**", files["summary.md"].decode())

    def test_reconciliation_needs_prior_context_and_support(self):
        item = self.reconciliation()
        for field, value in (("prior_evidence", "sources/paper.txt"),
                             ("status", "unresolved"), ("evidence", []), ("reason", "")):
            with self.subTest(field=field):
                self.review["reconciliations"] = [{**item, field: value}]
                with self.assertRaises(rr.InputError):
                    self.run_report()
        self.review["reconciliations"] = [item, item]
        with self.assertRaises(rr.InputError):
            self.run_report()

    def test_fresh_review_cannot_reconcile_an_unretained_prior_claim(self):
        self.review["reconciliations"] = [self.reconciliation()]
        self.review.update(context_policy="fresh", prior_reviews=[])
        with self.assertRaises(rr.InputError):
            self.run_report()

    def test_changed_head_procedure_or_source_makes_only_observation_stale(self):
        original = self.run_report()
        for field in ("head_commit", "procedure", "sources", "merge_base", "required_checks"):
            with self.subTest(field=field):
                current = copy.deepcopy(self.request)
                inputs = dict(self.inputs)
                if field in ("head_commit", "merge_base"):
                    current[field] = "c" * 40
                elif field == "required_checks":
                    current[field].append("proof")
                else:
                    path = current[field][0]["path"]
                    inputs[path] += b"changed\n"
                    current[field] = rr.descriptors({path: inputs[path]})
                current["id"] = rr.request_id(current)
                folder = self.root / field
                rr.write_directory(folder, inputs | {"request.json": rr.encode(current)})
                changed = self.run_report(folder)
                self.assertEqual(changed["report.json"], original["report.json"])
                observation = rr.parse(changed["observation.json"])
                self.assertEqual(observation["freshness"], "STALE")
                self.assertEqual(observation["completeness"], "incomplete")

    def test_old_results_cannot_attach_to_new_request(self):
        self.review["request_id"] = "c" * 64
        with self.assertRaisesRegex(rr.InputError, "another request"):
            self.run_report()
        self.review["request_id"] = self.request["id"]
        self.manifest["request_id"] = "c" * 64
        with self.assertRaisesRegex(rr.InputError, "another request"):
            self.run_report()

    def test_request_and_evidence_tampering_rejected(self):
        (self.evidence_dir / "evidence/build.json").write_bytes(b"changed")
        with self.assertRaisesRegex(rr.InputError, "digest mismatch"):
            self.run_report()
        (self.evidence_dir / "evidence/build.json").write_bytes(self.raw)
        (self.request_dir / "procedure/SKILL.md").write_bytes(b"changed")
        with self.assertRaisesRegex(rr.InputError, "digest mismatch"):
            self.run_report()

    def test_malformed_findings_and_unknown_fields_rejected(self):
        baseline = copy.deepcopy(self.review)
        for field, value in (("findings", "not an array"), ("verdict", "CLEAN"),
                             ("questions", [True])):
            with self.subTest(field=field):
                self.review = copy.deepcopy(baseline)
                self.review[field] = value
                with self.assertRaises(rr.InputError):
                    self.run_report()

    def test_invalid_finding_locations_and_evidence_rejected(self):
        for change in ({"line": True}, {"file": "outside.lean"}, {"evidence": []},
                       {"evidence": ["invented.json"]}, {"severity": "approve"}):
            with self.subTest(change=change):
                self.review["findings"] = [self.finding(**change)]
                with self.assertRaises(rr.InputError):
                    self.run_report()

    def test_duplicate_checks_and_missing_pass_evidence_rejected(self):
        self.manifest["checks"] *= 2
        with self.assertRaisesRegex(rr.InputError, "duplicate check"):
            self.run_report()
        self.manifest["checks"] = [self.manifest["checks"][0]]
        self.manifest["checks"][0]["evidence"] = []
        with self.assertRaisesRegex(rr.InputError, "evidence required"):
            self.run_report()

    def test_proof_policy_and_outcome_remain_visible(self):
        self.manifest["checks"].append({"kind": "proof", "status": "pass", "producer": "test verifier",
                                        "policy": "extra assumption H allowed", "detail": "Conditional fixture.",
                                        "evidence": ["evidence/build.json"]})
        files = self.run_report()
        self.assertIn("extra assumption H allowed", files["summary.md"].decode())
        self.assertNotIn("unconditional", files["summary.md"].decode())

    def test_rereviews_require_retained_prior_context(self):
        self.review["context_policy"] = "rereview"
        with self.assertRaisesRegex(rr.InputError, "evidence required"):
            self.run_report()
        self.review["prior_reviews"] = ["evidence/build.json"]
        self.assertEqual(self.report()["review"]["context_policy"], "rereview")
        self.review["context_policy"] = "fresh"
        with self.assertRaisesRegex(rr.InputError, "cannot carry"):
            self.run_report()

    def test_paths_symlinks_and_duplicate_json_keys_rejected(self):
        for name in ("../secret", "/secret", "evidence/../secret", "evidence//file", "a\\b"):
            with self.subTest(name=name), self.assertRaises(rr.InputError):
                rr.relative(name)
        path = self.evidence_dir / "evidence/build.json"
        path.unlink()
        path.symlink_to(self.request_dir / "sources/paper.txt")
        with self.assertRaisesRegex(rr.InputError, "symlink"):
            self.run_report()
        for raw in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":"\\ud800"}'):
            with self.subTest(raw=raw), self.assertRaises(rr.InputError):
                rr.parse(raw)

    def test_render_escapes_findings_and_does_not_overwrite(self):
        self.review["findings"] = [self.finding(message='<script> @someone [click](https://example.org)')]
        files = self.run_report()
        summary = files["summary.md"].decode()
        self.assertNotIn('<script>', summary)
        self.assertNotIn('@someone', summary)
        self.assertNotIn('[click](', summary)
        output = self.root / "report"
        rr.write_directory(output, files)
        with self.assertRaises(FileExistsError):
            rr.write_directory(output, {"report.json": b"overwrite"})
        self.assertEqual((output / "report.json").read_bytes(), files["report.json"])

    def test_prepare_uses_committed_git_scope_and_excludes_eval_keys(self):
        repo = self.root / "repo"
        repo.mkdir()
        def git(*args):
            return subprocess.run(['git', '-C', str(repo), *args], check=True,
                                  capture_output=True, text=True).stdout.strip()
        git('init', '-q')
        git('config', 'user.name', 'Test')
        git('config', 'user.email', 'test@example.invalid')
        (repo / 'Example.lean').write_text('base\n')
        git('add', '.')
        git('commit', '-qm', 'base')
        base = git('rev-parse', 'HEAD')
        (repo / 'Example.lean').write_text('PR\n')
        git('commit', '-qam', 'PR')
        (repo / 'untracked.txt').write_text('caller edit\n')
        skill = self.request_dir / 'procedure'
        (skill / 'evals').mkdir()
        (skill / 'evals/key.json').write_text('private answer key')
        files = rr.prepare(repo, 'owner/repo', base, skill, self.request_dir / 'sources', ['proof'])
        request = rr.parse(files['request.json'])
        self.assertEqual(request['scope'], ['Example.lean'])
        self.assertEqual(request['head_commit'], git('rev-parse', 'HEAD'))
        self.assertEqual(request['required_checks'], ['build', 'proof'])
        self.assertNotIn('procedure/evals/key.json', files)
        self.assertEqual((repo / 'untracked.txt').read_text(), 'caller edit\n')


if __name__ == '__main__':
    unittest.main()
