#!/usr/bin/env python3
"""Retain and reuse the Pages artifact from an exact-commit merge-queue build.

Only this workflow's successful merge_group runs can supply artifacts. A cache
miss (including API or integrity failures) leaves the website build enabled.
Lean validation and cache refresh run whether or not the website is reused.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.parse import urlencode
import zipfile

WORKFLOW = ".github/workflows/build-and-docs.yml"
RECEIPT = "queue-build-receipt"
MAX_ARCHIVE = 2 * 1024**3


def sha256(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def inputs():
    # The commit binds source, workflow, dependency pins, and build recipes.
    # Include environment inputs here if the workflow adds configurable feeds.
    return {
        "schema": 1,
        "repository": os.environ["GITHUB_REPOSITORY"],
        "sha": os.environ["GITHUB_SHA"],
        "workflow": WORKFLOW,
        "base_path": os.environ["BASE_PATH"],
        "runner_os": os.environ["RUNNER_OS"],
        "runner_image": os.environ["ImageOS"],
        "runner_image_version": os.environ["ImageVersion"],
        "build_mode": "full",
    }


class GitHub:
    def __init__(self, repository):
        self.root = f"repos/{repository}/actions"

    def get(self, path):
        result = subprocess.run(
            ["gh", "api", f"{self.root}/{path}"], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
        )
        return json.loads(result.stdout)

    def download(self, artifact_id, destination):
        with destination.open("wb") as stream:
            subprocess.run(
                ["gh", "api", f"{self.root}/artifacts/{artifact_id}/zip"],
                check=True, stdout=stream, stderr=subprocess.PIPE, timeout=180,
            )


def eligible(run, current, expected):
    return (
        run.get("event") == "merge_group"
        and run.get("status") == "completed"
        and run.get("conclusion") == "success"
        and run.get("head_sha") == expected["sha"]
        and run.get("path") == WORKFLOW
        and run.get("workflow_id") == current["workflow_id"]
        and run.get("repository", {}).get("id") == current["repository"]["id"]
        and run.get("head_repository", {}).get("id") == current["repository"]["id"]
        and run.get("head_branch", "").startswith("gh-readonly-queue/main/")
    )


def artifact_named(artifacts, name, run, repository_id):
    matches = [a for a in artifacts if a.get("name") == name]
    if len(matches) != 1:
        raise ValueError("missing or ambiguous artifact")
    artifact = matches[0]
    origin = artifact.get("workflow_run") or {}
    if (artifact.get("expired") is not False
            or not 0 < artifact.get("size_in_bytes", 0) <= MAX_ARCHIVE
            or origin.get("id") != run["id"]
            or origin.get("head_sha") != run["head_sha"]
            or origin.get("repository_id") != repository_id
            or origin.get("head_repository_id") != repository_id):
        raise ValueError("artifact provenance or availability mismatch")
    return artifact


def unpack(archive, name, destination, limit):
    # Copy a single named member. Never extract paths or execute archive content.
    with zipfile.ZipFile(archive) as bundle:
        if bundle.namelist() != [name]:
            raise ValueError("unexpected archive members")
        if bundle.getinfo(name).file_size > limit:
            raise ValueError("artifact is too large")
        with bundle.open(name) as source, destination.open("wb") as target:
            shutil.copyfileobj(source, target)


def reuse(api, expected, current, destination):
    query = urlencode({"event": "merge_group", "head_sha": expected["sha"],
                       "status": "success", "per_page": 10})
    runs = api.get(f"workflows/{current['workflow_id']}/runs?{query}")["workflow_runs"]
    for candidate in runs:
        # Refresh: list results can predate a rerun.
        run = api.get(f"runs/{candidate['id']}")
        if not eligible(run, current, expected):
            continue
        try:
            artifacts = api.get(f"runs/{run['id']}/artifacts?per_page=100")["artifacts"]
            repository_id = current["repository"]["id"]
            receipt_artifact = artifact_named(artifacts, RECEIPT, run, repository_id)
            pages = artifact_named(artifacts, "github-pages", run, repository_id)
            with tempfile.TemporaryDirectory() as temporary:
                work = Path(temporary)
                api.download(receipt_artifact["id"], work / "receipt.zip")
                unpack(work / "receipt.zip", "receipt.json", work / "receipt.json", 64 * 1024)
                receipt = json.loads((work / "receipt.json").read_text())
                if (receipt["inputs"] != expected or receipt["run_id"] != run["id"]
                        or receipt["run_attempt"] != run["run_attempt"]
                        or receipt["artifact_id"] != pages["id"]):
                    raise ValueError("receipt does not match this build or run attempt")
                api.download(pages["id"], work / "pages.zip")
                unpack(work / "pages.zip", "artifact.tar", work / "artifact.tar", MAX_ARCHIVE)
                if sha256(work / "artifact.tar") != receipt["tar_sha256"]:
                    raise ValueError("Pages archive digest mismatch")
                # A source rerun or cancellation during download invalidates reuse.
                after = api.get(f"runs/{run['id']}")
                if not eligible(after, current, expected) or after["run_attempt"] != run["run_attempt"]:
                    raise ValueError("source run changed during download")
                destination.mkdir(parents=True, exist_ok=True)
                shutil.move(work / "artifact.tar", destination / "artifact.tar")
            return run["id"]
        except (KeyError, TypeError, ValueError, OSError, zipfile.BadZipFile,
                subprocess.SubprocessError):
            print(f"Merge-queue run {run['id']} has no usable validated artifact; checking other runs.")
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["record", "reuse"])
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    expected = inputs()
    if args.operation == "record":
        if os.environ["GITHUB_EVENT_NAME"] != "merge_group":
            parser.error("only merge-group builds can record reuse receipts")
        args.directory.mkdir(parents=True, exist_ok=True)
        receipt = {
            "inputs": expected,
            "run_id": int(os.environ["GITHUB_RUN_ID"]),
            "run_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "artifact_id": int(os.environ["PAGES_ARTIFACT_ID"]),
            "tar_sha256": sha256(Path(os.environ["RUNNER_TEMP"]) / "artifact.tar"),
        }
        (args.directory / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        return

    run_id = None
    if (os.environ.get("GITHUB_EVENT_NAME") == "push"
            and os.environ.get("GITHUB_REF") == "refs/heads/main"):
        try:
            api = GitHub(expected["repository"])
            current = api.get(f"runs/{os.environ['GITHUB_RUN_ID']}")
            run_id = reuse(api, expected, current, args.directory)
        except (KeyError, TypeError, ValueError, OSError, zipfile.BadZipFile,
                subprocess.SubprocessError):
            print("Merge-queue artifact lookup unavailable; building the website normally.")
    message = (f"Reusing the website from validated merge-queue run {run_id} for {expected['sha']}. "
               "Lean validation and cache refresh remain enabled."
               if run_id else "No matching validated merge-queue artifact; building the website normally.")
    print(message)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"reused={'true' if run_id else 'false'}\n")
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
        summary.write(message + "\n")
        if run_id:
            summary.write(f"[Source validation and logs](https://github.com/{expected['repository']}/actions/runs/{run_id})\n")


if __name__ == "__main__":
    main()
