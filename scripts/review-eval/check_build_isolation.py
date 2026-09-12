#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Exercise real Docker/Lean build isolation without model calls or credentials."""

import argparse
import hashlib
import json
import secrets
import subprocess
from pathlib import Path

from workspace_server import WorkspaceTools


def check(image, output):
    image = subprocess.check_output(
        ["docker", "image", "inspect", image, "--format", "{{.Id}}"], text=True
    ).strip()
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "evidence").mkdir()
    candidate = output / "candidate.lean"
    header = b"""/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil
/-! # Build isolation test -/
namespace ReviewIsolation
/-- Check the frozen candidate rather than a replacement Lake target. -/
@[category test, AMS 11]
"""
    bad = header + b"theorem candidate : False := by trivial\nend ReviewIsolation\n"
    good = header + b"theorem candidate : True := True.intro\nend ReviewIsolation\n"
    candidate.write_bytes(bad)
    container = "fc-build-isolation-" + secrets.token_hex(6)
    module, path = (
        "FormalConjectures.ReviewIsolation",
        "FormalConjectures/ReviewIsolation.lean",
    )
    try:
        subprocess.run(
            [
                "docker",
                "run",
                "-d",
                "--name",
                container,
                "--network=none",
                "--cap-drop=ALL",
                "--security-opt=no-new-privileges",
                "--pids-limit=256",
                "--memory=6g",
                "--cpus=2",
                f"--mount=type=bind,src={candidate},dst=/workspace/{path},readonly",
                image,
            ],
            check=True,
            capture_output=True,
            timeout=30,
        )
        tools = WorkspaceTools(container, output, module, 30, image, candidate, path)
        results = {}
        results["invalid_candidate"] = tools.build()
        assert results["invalid_candidate"]["exit_code"] == 1
        results["poison_scratch"] = tools.execute(
            "printf '%s\\n' 'name = \"reviewProbe\"' '[[lean_lib]]' "
            f"'name = \"{module}\"' 'roots = []' > lakefile.toml; "
            f"lake --wfail build {module}"
        )
        assert results["poison_scratch"]["exit_code"] == 0
        results["isolated_after_poison"] = tools.build()
        assert results["isolated_after_poison"]["exit_code"] == 1
        assert candidate.read_bytes() == bad
        # A separately pinned valid candidate still builds. Each call starts from the image.
        valid = output / "valid.lean"
        valid.write_bytes(good)
        positive = WorkspaceTools(container, output, module, 30, image, valid, path)
        positive.counter = tools.counter
        results["valid_candidate"] = positive.build()
        assert results["valid_candidate"]["exit_code"] == 0
        results["valid_candidate_repeat"] = positive.build()
        assert results["valid_candidate_repeat"]["exit_code"] == 0
        result = {
            "status": "pass",
            "image": image,
            "cases": results,
            "tooling": {
                p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in (
                    Path(__file__),
                    Path(__file__).with_name("workspace_server.py"),
                )
            },
        }
        (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(
            "PASS: invalid candidate rejected after scratch tampering; valid candidate builds twice."
        )
    finally:
        subprocess.run(
            ["docker", "rm", "-f", container, container + "-build"],
            capture_output=True,
            check=False,
            timeout=15,
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    check(args.image, args.out)
