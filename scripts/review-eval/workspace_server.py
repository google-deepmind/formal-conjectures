#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy at https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""MCP tools for one isolated review container. Host paths and keys are never tools."""

import argparse
import hashlib
import json
import re
import subprocess
import threading
import time
from pathlib import Path


class WorkspaceTools:
    """Scratch commands and recorded builds have no shared writable filesystem."""

    def __init__(self, container, output, module, max_calls, image, candidate, candidate_path, timeout=60):
        if not isinstance(timeout, int) or not 1 <= timeout <= 300:
            raise ValueError("Tool timeout must be between 1 and 300 seconds")
        self.timeout = timeout
        if not re.fullmatch(r"sha256:[0-9a-f]{64}", image):
            raise ValueError("Build image must be pinned by image ID")
        path = Path(candidate_path)
        if (
            path.is_absolute()
            or ".." in path.parts
            or path.as_posix() != candidate_path
            or not candidate_path.startswith("FormalConjectures/")
            or not candidate_path.endswith(".lean")
            or "," in candidate_path
        ):
            raise ValueError("Invalid candidate path")
        self.container, self.output, self.module = container, Path(output), module
        self.max_calls, self.counter = max_calls, 0
        self.lock = threading.Lock()
        self.image, self.candidate = image, Path(candidate).resolve()
        if "," in str(self.candidate):
            raise ValueError("Candidate mount path cannot contain a comma")
        self.candidate_path = candidate_path
        self.binding = {
            "isolation": "fresh_container",
            "image": image,
            "module": module,
            "candidate_path": candidate_path,
            "candidate_sha256": hashlib.sha256(self.candidate.read_bytes()).hexdigest(),
        }

    def invoke(self, command, kind="command"):
        # Concurrent MCP requests must not reuse a build container or evidence filename.
        with self.lock:
            return self._invoke(command, kind)

    def _invoke(self, command, kind):
        if self.counter >= self.max_calls:
            raise ValueError("Tool-call budget exhausted")
        self.counter += 1
        build_container = self.container + "-build"
        if kind == "build":
            if (
                hashlib.sha256(self.candidate.read_bytes()).hexdigest()
                != self.binding["candidate_sha256"]
            ):
                raise ValueError("Candidate changed before build")
            invocation = [
                "docker",
                "run",
                "--rm",
                "--name",
                build_container,
                "--network=none",
                "--cap-drop=ALL",
                "--security-opt=no-new-privileges",
                "--pids-limit=256",
                "--memory=6g",
                "--cpus=2",
                "--workdir=/workspace",
                f"--mount=type=bind,src={self.candidate},dst=/workspace/{self.candidate_path},readonly",
                self.image,
                *command,
            ]
        else:
            invocation = [
                "docker",
                "exec",
                "-i",
                "-w",
                "/workspace",
                self.container,
                *command,
            ]
        started = time.monotonic()
        try:
            proc = subprocess.run(
                invocation,
                capture_output=True,
                timeout=self.timeout + 5,
                check=False,
            )
            record = {
                "kind": kind,
                "command": command,
                "exit_code": proc.returncode,
                "stdout": proc.stdout.decode(errors="replace"),
                "stderr": proc.stderr.decode(errors="replace"),
                "timed_out": proc.returncode == 124,
            }
        except subprocess.TimeoutExpired as error:
            record = {
                "kind": kind,
                "command": command,
                "exit_code": None,
                "stdout": (error.stdout or b"").decode(errors="replace"),
                "stderr": (error.stderr or b"").decode(errors="replace"),
                "timed_out": True,
            }
        finally:
            if kind == "build":
                # Also remove the fresh container after a host-side timeout or interrupted run.
                subprocess.run(
                    ["docker", "rm", "-f", build_container],
                    capture_output=True,
                    check=False,
                    timeout=10,
                )
        if kind == "build":
            record["environment"] = self.binding
        record["wall_seconds"] = round(time.monotonic() - started, 3)
        name = f"evidence/tool-{self.counter:03d}.json"
        (self.output / name).write_text(json.dumps(record, indent=2) + "\n")
        return {
            "evidence": name,
            **{k: v[:24000] if isinstance(v, str) else v for k, v in record.items()},
        }

    def execute(self, command: str) -> dict:
        """Run a shell command in the isolated workspace. Read files with cat/sed/rg;
        write scratch files under /output. Source documents are in /sources.
        Network and host filesystem are unavailable. Full output is retained as evidence.
        Use build() for the recorded focused build. Commands time out after 60 seconds.
        """
        return self.invoke(["timeout", "-k", "2", str(self.timeout), "sh", "-c", command])

    def build(self) -> dict:
        """Build the original candidate in a fresh pinned container, independent of scratch changes."""
        return self.invoke(
            ["timeout", "-k", "2", str(self.timeout), "lake", "--wfail", "build", self.module],
            "build",
        )


def serve(container, output, module, max_calls, image, candidate, candidate_path):
    from mcp.server.fastmcp import FastMCP

    server = FastMCP("review_workspace")
    tools = WorkspaceTools(container, output, module, max_calls, image, candidate, candidate_path)
    server.tool()(tools.execute)
    server.tool()(tools.build)
    server.run(transport="stdio")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--container", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--max-calls", type=int, default=30)
    parser.add_argument("--image", required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--candidate-path", required=True)
    args = parser.parse_args()
    serve(
        args.container,
        args.output,
        args.module,
        args.max_calls,
        args.image,
        args.candidate,
        args.candidate_path,
    )
