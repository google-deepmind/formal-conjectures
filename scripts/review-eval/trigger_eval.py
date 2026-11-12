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

"""Controlled description-routing experiment, separate from mathematical review scores.

Uses a real MCP load_skill call. This is not a measurement of native desktop auto-discovery.
"""
import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import review_eval as ev


def load_queries(path, split):
    queries = ev.read(path)
    ids = set()
    for query in queries:
        ev.rr.require(query["id"] not in ids and query["id"].isalnum(), "invalid query id")
        ids.add(query["id"])
        ev.rr.require(type(query["should_trigger"]) is bool and bool(query["query"].strip()), "invalid query")
        ev.rr.require(query["split"] in ("development", "validation"), "invalid query split")
    selected = [query for query in queries if query["split"] == split]
    ev.rr.require(bool(selected), "empty query selection")
    return selected


def loaded_skill(events):
    return any(
        e.get("type") == "item.completed"
        and e.get("item", {}).get("type") == "mcp_tool_call"
        and e["item"].get("server") == "review_workspace"
        and e["item"].get("tool") == "load_skill"
        and e["item"].get("status") == "completed"
        and e["item"].get("error") is None
        and not (e["item"].get("result") or {}).get("is_error", False)
        and not (e["item"].get("result") or {}).get("isError", False)
        for e in events
    )


def serve(skill):
    from mcp.server.fastmcp import FastMCP

    mcp = FastMCP("review_workspace")

    @mcp.tool()
    def load_skill() -> str:
        """Load the optional skill listed in the task's available-skill catalog."""
        return skill.read_text()

    mcp.run(transport="stdio")


def run(queries, skill, output, repeats, split, model):
    import yaml

    content = skill.read_text()
    metadata = yaml.safe_load(content.split("---", 2)[1])
    ev.rr.require(repeats > 0, "repeats must be positive")
    cases = load_queries(queries, split)
    output.mkdir(parents=True, exist_ok=False)
    (output / "SKILL.md").write_text(content)
    ev.write(output / "queries.json", cases)
    for source, relative in (
        (Path(ev.__file__), "review_eval.py"),
        (ev.HERE / "review_report.py", "review_report.py"),
        (Path(__file__), "review-eval/trigger_eval.py"),
    ):
        target = output / "tooling" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source.read_bytes())
    ev.write(
        output / "protocol.json",
        {
            "kind": "controlled MCP description routing; native client discovery unmeasured",
            "model": model,
            "repeats": repeats,
            "skill_sha256": ev.sha(content.encode()),
            "query_sha256": ev.sha(queries.read_bytes()),
            "tooling": ev.files(output / "tooling"),
        },
    )

    def one(job):
        q, n = job
        prompt = (
            q["query"]
            + "\n\nYou are starting this task. An optional skill is available:\n"
            + metadata["name"]
            + ": "
            + metadata["description"]
            + "\nUse load_skill if it would help with this task, then briefly state your next step. "
            "This routing exercise ends before you execute the task."
        )
        dest = output / (q["id"] + "-" + str(n))
        result = ev.invoke_model(
            prompt,
            dest,
            model,
            90,
            server_args=[
                str(output / "tooling/review-eval/trigger_eval.py"),
                "serve",
                "--skill",
                str(output / "SKILL.md"),
            ],
        )
        events = [json.loads(line) for line in (dest / "events.jsonl").read_text().splitlines()]
        loaded = loaded_skill(events)
        return {
            "id": q["id"],
            "repeat": n,
            "expected": q["should_trigger"],
            "loaded": loaded,
            "status": result["status"],
            "match": loaded == q["should_trigger"] if result["status"] == "completed" else None,
        }

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(one, [(q, n) for q in cases for n in range(repeats)]))
    ev.write(output / "results.json", results)
    print(
        json.dumps(
            {
                "scheduled": len(results),
                "completed": sum(r["status"] == "completed" for r in results),
                "matches": sum(r["match"] is True for r in results),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    s = sub.add_parser("serve")
    s.add_argument("--skill", type=Path, required=True)
    r = sub.add_parser("run")
    for field in ("queries", "skill", "out"):
        r.add_argument("--" + field, type=Path, required=True)
    r.add_argument("--repeats", type=int, default=3)
    r.add_argument("--split", choices=["development", "validation"], default="development")
    r.add_argument("--model", default="gpt-5.6-sol")
    a = parser.parse_args()
    if a.command == "serve":
        serve(a.skill)
    else:
        run(a.queries, a.skill, a.out.resolve(), a.repeats, a.split, a.model)
