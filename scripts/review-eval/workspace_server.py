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
import json
import subprocess
import time
from pathlib import Path


def serve(container, output, module, max_calls):
    from mcp.server.fastmcp import FastMCP

    server = FastMCP("review_workspace")
    output = Path(output)
    counter = 0

    def invoke(command, kind="command", stdin=None):
        nonlocal counter
        if counter >= max_calls:
            raise ValueError("Tool-call budget exhausted")
        counter += 1
        started = time.monotonic()
        try:
            proc = subprocess.run(
                ["docker", "exec", "-i", "-w", "/workspace", container, *command],
                input=stdin,
                capture_output=True,
                timeout=65,
                check=False,
            )
            record = {
                "kind": kind,
                "command": command,
                "exit_code": proc.returncode,
                "stdout": proc.stdout.decode(errors="replace"),
                "stderr": proc.stderr.decode(errors="replace"),
                "timed_out": False,
            }
        except subprocess.TimeoutExpired as error:
            # The outer timeout inside the container kills the command and its children.
            record = {
                "kind": kind,
                "command": command,
                "exit_code": None,
                "stdout": (error.stdout or b"").decode(errors="replace"),
                "stderr": (error.stderr or b"").decode(errors="replace"),
                "timed_out": True,
            }
        record["wall_seconds"] = round(time.monotonic() - started, 3)
        name = f"evidence/tool-{counter:03d}.json"
        (output / name).write_text(json.dumps(record, indent=2) + "\n")
        return {"evidence": name, **{k: v[:24000] if isinstance(v, str) else v for k, v in record.items()}}

    @server.tool()
    def execute(command: str) -> dict:
        """Run a shell command in the isolated workspace. Read files with cat/sed/rg;
        write scratch files under /output. Source documents are in /sources.
        Network and host filesystem are unavailable. Full output is retained as evidence.
        Use build() for the recorded focused build. Commands time out after 60 seconds.
        """
        return invoke(["timeout", "-k", "2", "60", "sh", "-c", command])

    @server.tool()
    def build() -> dict:
        """Run lake --wfail build on the original review module and retain the exact result."""
        return invoke(["timeout", "-k", "2", "60", "lake", "--wfail", "build", module], "build")

    server.run(transport="stdio")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--container", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--max-calls", type=int, default=30)
    args = parser.parse_args()
    serve(args.container, args.output, args.module, args.max_calls)
