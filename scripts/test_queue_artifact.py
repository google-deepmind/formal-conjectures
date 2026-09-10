"""Exercise artifact promotion and safe misses without a Lean build or network."""

import copy
import hashlib
import json
import os
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


if __name__ == "__main__":
    unittest.main()
