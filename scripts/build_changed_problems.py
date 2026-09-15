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

"""Plan and check a targeted problem-only PR build.

All other changes and events retain full validation. Importers, aggregate
conflicts, and repository-wide checks are deferred to the full merge-queue build.
"""

import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

MAX_FILES = 20
EXCLUDES = "--exclude=statement,docstring,moduleDocstrings,fileFirstAdded,fileLastModified"


def git(*args):
    return subprocess.run(["git", *args], check=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE).stdout.decode("utf-8")


def plan_scope(event):
    def full(reason):
        return {"targeted": False, "reason": reason, "files": []}
    if event != "pull_request":
        return full("Only pull-request events use targeted validation.")
    try:
        parents = git("rev-list", "--parents", "-n", "1", "HEAD").split()
        if len(parents) != 3:
            return full("Checkout is not a two-parent PR merge commit.")
        # Inspect every changed path, not just the problem directory. Disabling
        # rename detection represents renames as delete/add, which forces full CI.
        raw = git("diff", "--raw", "-z", "--no-renames", parents[1], parents[0], "--")
        fields = raw.split("\0")
        if fields.pop() != "" or len(fields) % 2:
            return full("Cannot interpret the complete changed-file scope.")
        paths = []
        for record, path in zip(fields[::2], fields[1::2]):
            old_mode, new_mode, _, _, status = record.split()
            if (status not in ("A", "M") or new_mode != "100644"
                    or old_mode not in (":000000", ":100644")
                    or not path.startswith("FormalConjectures/")
                    or not path.endswith(".lean") or path == "FormalConjectures/All.lean"):
                return full("Scope includes a non-problem change, deletion, rename, or file-type change.")
            paths.append(path)
        if not paths or len(paths) > MAX_FILES:
            return full(f"Targeted validation requires 1–{MAX_FILES} added/modified problem files.")
        return {"targeted": True, "reason": "Only ordinary problem files changed.",
                "files": sorted(paths), "head": parents[0]}
    except (subprocess.CalledProcessError, UnicodeError, ValueError):
        return full("Changed-file scope is unavailable; use full validation.")


def describe(scope):
    if scope["targeted"]:
        return ("Targeted PR validation: " + shlex.join(scope["files"]) + "\n"
                "Build dependencies and category checks are included. Importers, aggregate "
                "conflicts, and repository-wide tests wait for full merge-queue validation.")
    return "Full validation: " + scope["reason"]


def check_scope(scope, out):
    # Recompute from Git so an incomplete or outdated file list cannot select a
    # smaller scope than this PR. Never turn a failed targeted check into success.
    if not scope.get("targeted") or scope != plan_scope(os.environ.get("GITHUB_EVENT_NAME")):
        raise ValueError("Targeted scope no longer matches this PR checkout.")
    out.mkdir(parents=True, exist_ok=True)
    scripts = Path(__file__).parent
    print(describe(scope), flush=True)
    subprocess.run([sys.executable, str(scripts / "lake-build-wrapper.py"),
                    str(out / "build.json"), "lake", "--wfail", "build", *scope["files"]], check=True)
    extractions = []
    # The native exporter accepts one file per invocation. Preserve its output
    # separately; these scoped diagnostics are never published as a full catalog.
    for index, path in enumerate(scope["files"]):
        metadata = out / f"metadata-{index:03d}.json"
        with metadata.open("w") as stream:
            subprocess.run(["lake", "exe", "extract_names", path, EXCLUDES],
                           stdout=stream, check=True)
        extractions.append(str(metadata))
    subprocess.run([sys.executable, str(scripts / "check_category_warnings.py"),
                    *extractions], check=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="Select full or targeted validation from the event and Git diff")
    plan.add_argument("--out", required=True, type=Path, help="Scope JSON file")
    check = commands.add_parser("check", help="Build selected files and check their native metadata")
    check.add_argument("--plan", required=True, type=Path, help="Scope JSON from the plan operation")
    check.add_argument("--out", required=True, type=Path, help="Directory for build and metadata diagnostics")
    args = parser.parse_args(argv)
    if args.command == "plan":
        scope = plan_scope(os.environ.get("GITHUB_EVENT_NAME"))
        args.out.write_text(json.dumps(scope, indent=2) + "\n")
        message = describe(scope)
        print(message)
        if output := os.environ.get("GITHUB_OUTPUT"):
            with open(output, "a") as stream:
                stream.write(f"targeted={str(scope['targeted']).lower()}\n")
        if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(summary, "a") as stream:
                stream.write(message + "\n")
        return 0
    try:
        check_scope(json.loads(args.plan.read_text()), args.out)
        return 0
    except subprocess.CalledProcessError as error:
        return error.returncode
    except (OSError, ValueError) as error:
        print(f"Targeted validation failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
