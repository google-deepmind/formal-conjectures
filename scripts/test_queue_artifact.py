"""Exercise artifact promotion and safe misses without a Lean build or network."""

import copy
import hashlib
import json
import os
import re
import subprocess
import textwrap
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import queue_artifact as qa


class FakeGitHub:
    def __init__(self):
        self.expected = {"schema": 1, "repository": "owner/repo", "sha": "a" * 40,
                         "workflow": qa.WORKFLOW, "base_path": "/formal-conjectures",
                         "runner_os": "Linux", "build_mode": "full"}
        self.current = {"workflow_id": 10, "repository": {"id": 20}}
        self.run = {**self.current, "id": 30, "run_attempt": 1,
                    "event": "merge_group", "status": "completed", "conclusion": "success",
                    "head_sha": self.expected["sha"], "path": qa.WORKFLOW,
                    "head_repository": {"id": 20}, "head_branch": "gh-readonly-queue/main/pr-1-abc"}
        self.tar = b"exact Pages tar bytes"
        self.receipt = {"inputs": self.expected.copy(), "run_id": 30, "run_attempt": 1,
                        "artifact_id": 40, "tar_sha256": hashlib.sha256(self.tar).hexdigest()}
        origin = {"id": 30, "head_sha": self.expected["sha"],
                  "repository_id": 20, "head_repository_id": 20}
        self.artifacts = [{"id": id_, "name": name, "expired": False,
                           "size_in_bytes": 1000, "workflow_run": origin.copy()}
                          for id_, name in [(40, "github-pages"), (41, qa.RECEIPT)]]
        self.fail_download = False
        self.extra_member = False
        self.run_reads = 0
        self.rerun_during_download = False

    def get(self, path):
        if path.startswith("workflows/"):
            return {"workflow_runs": [self.run]}
        if "/artifacts?" in path:
            return {"artifacts": self.artifacts}
        self.run_reads += 1
        run = copy.deepcopy(self.run)
        if self.rerun_during_download and self.run_reads > 1:
            run["run_attempt"] += 1
        return run

    def download(self, artifact_id, destination):
        if self.fail_download:
            raise OSError("download failed")
        with zipfile.ZipFile(destination, "w") as bundle:
            if artifact_id == 40:
                bundle.writestr("artifact.tar", self.tar)
                if self.extra_member:
                    bundle.writestr("../unexpected", "unsafe")
            else:
                bundle.writestr("receipt.json", json.dumps(self.receipt))


class ReuseTest(unittest.TestCase):
    def setUp(self):
        self.api = FakeGitHub()
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.destination = Path(self.temp.name) / "promoted"

    def reuse(self):
        return qa.reuse(self.api, self.api.expected, self.api.current, self.destination)

    def assert_miss(self):
        self.assertIsNone(self.reuse())
        self.assertFalse((self.destination / "artifact.tar").exists())

    def test_success_copies_exact_tar(self):
        self.assertEqual(self.reuse(), 30)
        self.assertEqual((self.destination / "artifact.tar").read_bytes(), self.api.tar)

    def test_only_successful_exact_commit_queue_runs_are_eligible(self):
        for key, value in [("event", "pull_request"), ("event", "push"),
                           ("status", "in_progress"), ("conclusion", "failure"),
                           ("conclusion", "cancelled"), ("head_sha", "b" * 40),
                           ("workflow_id", 99), ("path", ".github/workflows/other.yml"),
                           ("repository", {"id": 99}), ("head_repository", {"id": 99}),
                           ("head_branch", "gh-readonly-queue/other/pr-1")]:
            with self.subTest(key=key, value=value):
                self.api = FakeGitHub()
                self.api.run[key] = value
                self.assert_miss()

    def test_missing_ambiguous_expired_and_foreign_artifacts(self):
        for change in [lambda a: a.clear(), lambda a: a.append(a[0].copy()),
                       lambda a: a[0].update(expired=True),
                       lambda a: a[0].update(size_in_bytes=qa.MAX_ARCHIVE + 1),
                       lambda a: a[0]["workflow_run"].update(head_repository_id=99),
                       lambda a: a[0]["workflow_run"].update(head_sha="b" * 40),
                       lambda a: a[0]["workflow_run"].update(id=99)]:
            self.api = FakeGitHub()
            change(self.api.artifacts)
            self.assert_miss()

    def test_receipt_binds_build_inputs_and_attempt(self):
        for key, value in [("inputs", {"schema": 0}), ("run_id", 99),
                           ("run_attempt", 2), ("artifact_id", 99),
                           ("tar_sha256", "bad")]:
            with self.subTest(key=key):
                self.api = FakeGitHub()
                self.api.receipt[key] = value
                self.assert_miss()

    def test_unavailable_or_unsafe_archive_falls_back(self):
        for flag in ["fail_download", "extra_member", "rerun_during_download"]:
            self.api = FakeGitHub()
            setattr(self.api, flag, True)
            self.assert_miss()

    def test_old_workflows_without_receipts_build_normally(self):
        self.api.artifacts.pop()
        self.assert_miss()

    def test_size_checked_before_unzip(self):
        archive = Path(self.temp.name) / "large.zip"
        with zipfile.ZipFile(archive, "w") as bundle:
            bundle.writestr("receipt.json", "x" * 100)
        with self.assertRaises(ValueError):
            qa.unpack(archive, "receipt.json", Path(self.temp.name) / "out", 10)

    def test_api_failure_records_miss(self):
        env = {"GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "a" * 40,
               "BASE_PATH": "/formal-conjectures", "RUNNER_OS": "Linux",
               "ImageOS": "ubuntu24", "ImageVersion": "20260907.1",
               "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main",
               "GITHUB_RUN_ID": "100", "GITHUB_OUTPUT": self.temp.name + "/output",
               "GITHUB_STEP_SUMMARY": self.temp.name + "/summary"}
        with patch.dict(os.environ, env), patch("sys.argv", ["queue_artifact.py", "reuse", str(self.destination)]), \
                patch.object(qa.GitHub, "get", side_effect=OSError("unavailable")):
            qa.main()
        self.assertEqual(Path(env["GITHUB_OUTPUT"]).read_text(), "reused=false\n")
        self.assertFalse(self.destination.exists())

    def test_other_events_never_query_artifacts(self):
        env = {"GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "a" * 40,
               "BASE_PATH": "/formal-conjectures", "RUNNER_OS": "Linux",
               "ImageOS": "ubuntu24", "ImageVersion": "20260907.1",
               "GITHUB_EVENT_NAME": "workflow_dispatch", "GITHUB_REF": "refs/heads/main",
               "GITHUB_OUTPUT": self.temp.name + "/output", "GITHUB_STEP_SUMMARY": self.temp.name + "/summary"}
        with patch.dict(os.environ, env), patch("sys.argv", ["queue_artifact.py", "reuse", str(self.destination)]), \
                patch.object(qa.GitHub, "get") as get:
            qa.main()
        get.assert_not_called()

    def test_record_binds_tar_and_runner_image(self):
        env = {"GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "a" * 40,
               "BASE_PATH": "/formal-conjectures", "RUNNER_OS": "Linux",
               "ImageOS": "ubuntu24", "ImageVersion": "20260907.1",
               "GITHUB_EVENT_NAME": "merge_group", "GITHUB_RUN_ID": "30",
               "GITHUB_RUN_ATTEMPT": "2", "PAGES_ARTIFACT_ID": "40",
               "RUNNER_TEMP": self.temp.name}
        (Path(self.temp.name) / "artifact.tar").write_bytes(self.api.tar)
        with patch.dict(os.environ, env), patch("sys.argv", ["queue_artifact.py", "record", str(self.destination)]):
            qa.main()
        receipt = json.loads((self.destination / "receipt.json").read_text())
        self.assertEqual(receipt["tar_sha256"], hashlib.sha256(self.api.tar).hexdigest())
        self.assertEqual(receipt["run_attempt"], 2)
        self.assertEqual(receipt["inputs"]["runner_image_version"], "20260907.1")


class WorkflowReuseTest(unittest.TestCase):
    """Run the real mode script and check the workflow's build-step conditions.

    This covers successful-job selection, not a simulation of the Actions runner.
    actionlint and live qualification cover the rest of the workflow contract.
    """

    @classmethod
    def setUpClass(cls):
        default = Path(__file__).resolve().parents[1] / ".github/workflows/build-and-docs.yml"
        cls.workflow = Path(os.environ.get("FC_BUILD_WORKFLOW", default)).read_text()
        build = cls.workflow.split("  build:\n", 1)[1].split("  # Deployment job", 1)[0]
        cls.steps = dict(re.findall(
            r"^      - name: ([^\n]+)\n(.*?)(?=^      - name: |\Z)", build, re.M | re.S))

    def mode(self, reused, website_only="", event="push", ref="main"):
        step = self.steps["Detect build mode"]
        match = re.search(r"        run: \|\n((?:          .*\n|\n)+)", step)
        self.assertIsNotNone(match)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "output"
            env = {**os.environ, "GITHUB_OUTPUT": str(output), "REUSED_SITE": reused,
                   "WEBSITE_ONLY": website_only, "EVENT_NAME": event, "REF_NAME": ref}
            subprocess.run(["bash", "-eu", "-c", textwrap.dedent(match[1])],
                           env=env, cwd=directory, capture_output=True, check=True)
            return dict(line.split("=", 1) for line in output.read_text().splitlines())

    def enabled(self, name, mode, reused, event="push"):
        condition = re.search(r"^        if: (.+)$", self.steps[name], re.M)
        if condition is None:
            return True
        values = {"steps.mode.outputs.website_only": mode["website_only"],
                  "steps.mode.outputs.site": mode["site"],
                  "steps.reuse.outputs.reused": reused, "github.event_name": event}
        expression = condition[1]
        for key, value in values.items():
            expression = expression.replace(key, "'" + value + "'")
        # All tested conditions use the shared ==, !=, && subset of Actions/bash.
        self.assertNotRegex(expression, r"steps\.|github\.|always\(|failure\(")
        result = subprocess.run(["bash", "-c", "[[ " + expression + " ]]"], capture_output=True)
        self.assertIn(result.returncode, (0, 1), result.stderr)
        return result.returncode == 0

    def test_reuse_preserves_lean_and_cache_but_skips_site(self):
        mode = self.mode("true")
        self.assertEqual(mode, {"website_only": "false", "site": "false"})
        required = ["Install elan", "Get olean cache", "Build ForMathlib, utilities, and test",
                    "Build problems", "Pack olean cache", "Save ~/.cache/mathlib",
                    "Generate conjectures data for website", "Check category warnings",
                    "Upload reused deploy artifact"]
        required += [name for name in ("Restore local lake build", "Save local lake build",
                                      "Restore Lean build", "Save Lean build") if name in self.steps]
        self.assertTrue(any(name.startswith("Save ") and "build" in name for name in required))
        for name in required:
            with self.subTest(step=name):
                self.assertTrue(self.enabled(name, mode, "true"))
        skipped = ["Build literate source pages", "Post-process literate HTML",
                   "Install Python dependencies", "Run plotting script", "Set up Node.js",
                   "Extract Verso fragments for website", "Build website",
                   "Assemble deploy artifact", "Upload deploy artifact", "Download live site data"]
        skipped += [name for name in ("Initialize documentation workspace", "Restore documentation tools",
                                     "Restore literate data", "Save documentation tools", "Save literate data")
                    if name in self.steps]
        for name in skipped:
            with self.subTest(step=name):
                self.assertFalse(self.enabled(name, mode, "true"))

    def test_missing_or_failed_lookup_builds_site(self):
        for reused in ("false", ""):
            mode = self.mode(reused)
            self.assertEqual(mode, {"website_only": "false", "site": "true"})
            for name in ("Build problems", "Build literate source pages", "Build website", "Upload deploy artifact"):
                self.assertTrue(self.enabled(name, mode, reused))
            self.assertFalse(self.enabled("Upload reused deploy artifact", mode, reused))

    def test_manual_and_website_preview_modes(self):
        self.assertEqual(self.mode("", event="workflow_dispatch"),
                         {"website_only": "false", "site": "true"})
        for options in ({"website_only": "true", "event": "workflow_dispatch"}, {"ref": "example-webtest"}):
            mode = self.mode("", **options)
            self.assertEqual(mode, {"website_only": "true", "site": "true"})
            self.assertFalse(self.enabled("Build problems", mode, ""))
            self.assertTrue(self.enabled("Download live site data", mode, ""))

    def test_deployment_keeps_current_validation_dependency(self):
        deploy = self.workflow.split("  deploy:\n", 1)[1]
        self.assertIn("needs: [build, scripts]", deploy)
        self.assertNotIn("always()", deploy)
        for name in ("Build ForMathlib, utilities, and test", "Build problems", "Check category warnings",
                     "Upload reused deploy artifact"):
            self.assertNotIn("continue-on-error:", self.steps[name])
            self.assertNotIn("always()", self.steps[name])


if __name__ == "__main__":
    unittest.main()
