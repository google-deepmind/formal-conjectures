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

"""Tool-using review evaluations. See scripts/review-eval/README.md."""
import argparse
import hashlib
import importlib.metadata
import json
import os
import random
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import review_report as rr

HERE = Path(__file__).resolve().parent
VERSION = "fc.review-eval.v2"


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n").encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return rr.read_json(Path(path))


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(encode(value))


def asset(root, name):
    path = Path(root).resolve()
    for part in Path(rr.relative(name)).parts:
        path /= part
        rr.require(not path.is_symlink(), "symlink asset")
    return path.read_bytes()


def load_suite(path):
    suite = read(path)
    rr.require(suite["schema_version"] == VERSION, "unsupported suite")
    ids, families = set(), {}
    for c in suite["cases"]:
        rr.require(bool(re.fullmatch(r"[a-zA-Z0-9_-]+", c["id"])) and c["id"] not in ids, "invalid case id")
        ids.add(c["id"])
        rr.relative(c["path"])
        rr.require(
            c["path"].startswith("FormalConjectures/") and c["path"].endswith(".lean"),
            "candidate must be a problem module",
        )
        rr.require(c["split"] in ("development", "qualification"), "invalid split")
        rr.require(families.setdefault(c["family"], c["split"]) == c["split"], "family crosses splits")
        rr.require(c["kind"] in ("defect", "clean", "uncertainty", "rereview"), "invalid kind")
        rr.require(c["gold"]["status"] in ("provisional", "human_adjudicated"), "invalid gold status")
        if c["gold"]["status"] == "human_adjudicated":
            rr.require(
                bool(c["gold"].get("reviewer")) and bool(c["gold"].get("evidence")), "missing adjudication"
            )
        defect_ids = [d["id"] for d in c["gold"]["defects"]]
        rr.require(len(defect_ids) == len(set(defect_ids)), "duplicate defect ids")
        for name in [c["candidate"], *c["sources"].values(), *c.get("context", {}).values()]:
            rr.require(name in suite["assets"], "unfrozen case asset")
    rr.require(bool(ids), "empty suite")
    for name, digest in suite["assets"].items():
        rr.require(sha(asset(Path(path).parent, name)) == digest, "asset digest mismatch")
    return suite


def files(root):
    return {
        p.relative_to(root).as_posix(): sha(p.read_bytes()) for p in sorted(root.rglob("*")) if p.is_file()
    }


def freeze(suite_path, skill, output, image, cases, repeats, timeout, max_calls):
    suite = load_suite(suite_path)
    rr.require(repeats > 0 and timeout > 0 and max_calls > 0, "budgets must be positive")
    selected = [c for c in suite["cases"] if c["id"] in cases] if cases else suite["cases"]
    rr.require(bool(selected) and (not cases or len(selected) == len(set(cases))), "unknown case selection")
    if any(c["split"] == "qualification" for c in selected):
        rr.require(
            all(c["gold"]["status"] == "human_adjudicated" for c in selected),
            "qualification cases require human-adjudicated keys before runs",
        )
    image_id = subprocess.check_output(
        ["docker", "image", "inspect", image, "--format", "{{.Id}}"], text=True
    ).strip()
    rev = subprocess.check_output(
        ["docker", "run", "--rm", "--network", "none", image_id, "cat", "/workspace/.fc-revision"], text=True
    ).strip()
    rr.require(rev == suite["environment_commit"], "image has a different FC environment")
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    write(output / "suite.json", suite)
    for relative in ("review_eval.py", "review_report.py", "review-eval/workspace_server.py"):
        target = output / "tooling" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE / relative, target)
    for name in suite["assets"]:
        dest = output / "private-assets" / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(asset(Path(suite_path).parent, name))
    procedure = rr.collect(skill, "procedure", exclude_evals=True)
    rr.write_directory(output / "skill", {k.removeprefix("procedure/"): v for k, v in procedure.items()})
    jobs = [
        {"id": secrets.token_hex(8), "case": c["id"], "family": c["family"], "arm": arm, "repeat": n}
        for c in selected
        for n in range(repeats)
        for arm in ("skill", "baseline")
    ]
    random.SystemRandom().shuffle(jobs)
    write(
        output / "manifest.json",
        {
            "schema_version": VERSION,
            "image": image_id,
            "jobs": jobs,
            "timeout": timeout,
            "max_calls": max_calls,
            "frozen_files": files(output),
            "tooling": {
                p.name: sha(p.read_bytes())
                for p in [Path(__file__), HERE / "review_report.py", HERE / "review-eval/workspace_server.py"]
            },
        },
    )


def verify(root, *, check_tooling=True):
    m = read(root / "manifest.json")
    if check_tooling:
        for p in [Path(__file__), HERE / "review_report.py", HERE / "review-eval/workspace_server.py"]:
            rr.require(sha(p.read_bytes()) == m["tooling"][p.name], "tooling changed since freeze")
    for name, digest in m["frozen_files"].items():
        rr.require(sha(asset(root, name)) == digest, "frozen inputs changed")
    return m


def docker(*args, **kwargs):
    return subprocess.run(["docker", *args], check=True, capture_output=True, **kwargs)


def review_schema(request, max_calls=30, context=()):
    string = {"type": "string"}

    def obj(props):
        return {"type": "object", "properties": props, "required": list(props), "additionalProperties": False}

    def arr(item):
        return {"type": "array", "items": item}

    def enum(values):
        return {"type": "string", "enum": values}

    evidence_paths = [item["path"] for item in request.get("sources", [])]
    evidence_paths += [f"evidence/tool-{n:03d}.json" for n in range(1, max_calls + 1)]
    evidence_paths += list(context)
    evidence = {"type": "array", "items": enum(evidence_paths), "minItems": 1}

    return obj(
        {
            "request_id": enum([request["id"]]),
            "reviewer": string,
            "context_policy": enum(["fresh", "rereview"]),
            "prior_reviews": arr(string),
            "coverage": obj(
                {
                    k: enum(["complete", "incomplete"])
                    for k in ("source-fidelity", "statement-soundness", "metadata-hygiene")
                }
            ),
            "findings": arr(
                obj(
                    {
                        "angle": enum(["source-fidelity", "statement-soundness", "metadata-hygiene"]),
                        "file": enum(request["scope"]),
                        "line": {"type": "integer", "minimum": 0},
                        "severity": enum(["semantic", "nit"]),
                        "message": string,
                        "suggestion": string,
                        "evidence": evidence,
                    }
                )
            ),
            "questions": arr(string),
            "reconciliations": arr(
                obj(
                    {
                        "prior_evidence": string,
                        "status": enum(["retained", "corrected", "withdrawn"]),
                        "reason": string,
                        "evidence": evidence,
                    }
                )
            ),
        }
    )


def prompt(case, request, arm, model):
    # The shared prompt specifies task, environment and transport only, not review strategy.
    text = (
        case["prompt"] + "\n\nThe workspace is an isolated evaluation checkout at /workspace. "
        "The original file is read-only. Use the workspace tools; scratch files go in /output. "
        "Read AGENTS.md and the ordinary contribution guidance. Source snapshots are available "
        "on demand in /sources; networking is disabled equally for both conditions. "
        "Do not publish a review. Your final answer must follow the supplied JSON schema. "
        "Evidence references are sources/<filename> or evidence/tool-NNN.json returned by tools. "
        "Each evidence entry must be an exact path, without commentary; explain its relevance in message or reason. "
        "Use build() to record a focused build; other shell output is retained but not classified as a build.\n"
        f"Request id: {request['id']}; reviewer: {model}; context_policy: {case['context_policy']}; "
        f"prior_reviews: {json.dumps(list(case.get('context', {})))}.\n"
    )
    if arm == "skill":
        text += "Use the review skill at /skill/SKILL.md; read supporting files as needed.\n"
    return text


def review_procedure(skill, arm):
    if arm == "skill":
        return rr.collect(skill, "procedure")
    # The report requires a procedure receipt. This records the control condition;
    # it is not mounted into the reviewer workspace or added to the baseline prompt.
    return {
        "procedure/SKILL.md": b"# Unassisted baseline\n\nNo optional review skill was supplied. "
        b"The reviewer received the case prompt, JSON interface and ordinary FC guidance "
        b"from the pinned environment.\n"
    }


def allowed_call(call):
    if call.get("type") != "mcp_tool_call":
        return False
    if call.get("server") == "review_workspace":
        return True
    # Codex exposes built-in resource discovery even with plugins disabled. Only an
    # empty catalog is admissible; imported host resources invalidate the invocation.
    keys = {"list_mcp_resources": "resources", "list_mcp_resource_templates": "resourceTemplates"}
    if call.get("server") == "codex" and call.get("tool") in keys:
        content = (call.get("result") or {}).get("content", [])
        try:
            return len(content) == 1 and json.loads(content[0]["text"]) == {keys[call["tool"]]: []}
        except (KeyError, TypeError, ValueError):
            return False
    return False


def invoke_model(prompt_text, destination, model, timeout, schema=None, server_args=None):
    destination.mkdir(parents=True, exist_ok=False)
    (destination / "prompt.txt").write_text(prompt_text)
    args = [
        "codex",
        "exec",
        "--ignore-user-config",
        "--ignore-rules",
        "--ephemeral",
        "--skip-git-repo-check",
        "--sandbox",
        "read-only",
        "--model",
        model,
        "-c",
        'model_reasoning_effort="high"',
        "-c",
        "features.shell_tool=false",
        "-c",
        "features.unified_exec=false",
        "-c",
        "features.multi_agent=false",
        "-c",
        "features.apps=false",
        "-c",
        "features.plugins=false",
        "-c",
        "features.remote_plugin=false",
        "-c",
        "features.browser_use=false",
        "-c",
        "features.in_app_browser=false",
        "-c",
        "features.skill_search=false",
        "-c",
        'web_search="disabled"',
        "--json",
        "-o",
        str(destination / "answer.json"),
    ]
    # --ignore-user-config alone still discovers installed skills. Disable their catalogs
    # for this invocation, without editing the user's configuration or credentials.
    installed = set()
    for folder in (
        Path.home() / ".codex/skills",
        Path.home() / ".agents/skills",
        Path.home() / ".codex/plugins/cache",
    ):
        installed.update(str(p.parent) for p in folder.rglob("SKILL.md"))
    overrides = ",".join("{path=" + json.dumps(p) + ",enabled=false}" for p in sorted(installed))
    args += ["-c", "skills.config=[" + overrides + "]"]
    if schema:
        write(destination / "schema.json", schema)
        args += ["--output-schema", str(destination / "schema.json")]
    if server_args:
        args += [
            "-c",
            f"mcp_servers.review_workspace.command={json.dumps(sys.executable)}",
            "-c",
            f"mcp_servers.review_workspace.args={json.dumps(server_args)}",
            "-c",
            'mcp_servers.review_workspace.default_tools_approval_mode="approve"',
            "-c",
            "mcp_servers.review_workspace.required=true",
            "-c",
            "mcp_servers.review_workspace.tool_timeout_sec=75",
        ]
    args += ["-"]
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="fc-review-engine-") as temp:
        # A per-process Codex configuration directory prevents plugin and skill cache
        # discovery from importing the caller's review context. Authentication stays
        # in the existing host store and is never mounted into the reviewer container.
        engine_directory = Path(temp) / "codex"
        engine_directory.mkdir(mode=0o700)
        auth = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex")) / "auth.json"
        if auth.exists():
            (engine_directory / "auth.json").symlink_to(auth.resolve())
        engine_env = {k: v for k, v in os.environ.items() if k not in ("CODEX_SESSION_ID", "CODEX_THREAD_ID")}
        engine_env["CODEX_HOME"] = str(engine_directory)
        with (destination / "events.jsonl").open("w") as out, (destination / "stderr.txt").open("w") as err:
            proc = subprocess.Popen(
                args,
                cwd=temp,
                env=engine_env,
                stdin=subprocess.PIPE,
                stdout=out,
                stderr=err,
                start_new_session=True,
            )
            try:
                proc.communicate(prompt_text.encode(), timeout=timeout)
                status = "completed" if proc.returncode == 0 else "provider_error"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
                status = "timeout"
    events = [json.loads(line) for line in (destination / "events.jsonl").read_text().splitlines()]
    usage = [e["usage"] for e in events if e.get("type") == "turn.completed"]
    calls = [
        e["item"]
        for e in events
        if e.get("type") == "item.completed"
        and e.get("item", {}).get("type") not in ("reasoning", "agent_message", "error")
    ]
    if any(not allowed_call(c) for c in calls):
        status = "unexpected_tool"
    elif any(
        c.get("error") is not None
        or (c.get("result") or {}).get("is_error")
        or (c.get("result") or {}).get("isError")
        for c in calls
    ):
        status = "tool_transport_error"
    record = {
        "status": status,
        "model": model,
        "wall_seconds": round(time.monotonic() - start, 3),
        "usage": usage,
        "cost_usd": None,
        "tool_calls": len(calls),
        "command": args,
        "cli_version": subprocess.check_output(["codex", "--version"], text=True).strip(),
        "mcp_version": importlib.metadata.version("mcp") if server_args else None,
    }
    write(destination / "invocation.json", record)
    return record


def run_one(root, manifest, job, model):
    case = next(c for c in read(root / "suite.json")["cases"] if c["id"] == job["case"])
    out = root / "runs" / job["id"]
    if out.exists():
        # Never overwrite or silently retry a failed/interrupted attempt.
        return
    out.mkdir(parents=True)
    (out / "evidence").mkdir()
    sources = {
        "sources/" + name: asset(root / "private-assets", path) for name, path in case["sources"].items()
    }
    context = {name: asset(root / "private-assets", path) for name, path in case.get("context", {}).items()}
    procedure = review_procedure(root / "skill", job["arm"])
    candidate = asset(root / "private-assets", case["candidate"])
    # Isolated Git snapshots preserve provenance separately from the historical source commit.
    with tempfile.TemporaryDirectory(prefix="fc-review-snapshot-") as temp:
        repo = Path(temp)
        target = repo / case["path"]
        target.parent.mkdir(parents=True)
        target.write_bytes(candidate)

        def git(*args):
            env = os.environ | {
                "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
                "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
            }
            return (
                subprocess.check_output(["git", "-C", str(repo), *args], env=env, stderr=subprocess.DEVNULL)
                .decode()
                .strip()
            )

        git("init", "-q")
        git("config", "user.name", "Evaluation")
        git("config", "user.email", "eval@localhost")
        git("commit", "-q", "--allow-empty", "-m", "Base")
        base = git("rev-parse", "HEAD")
        git("branch", "origin/main")
        git("add", ".")
        git("commit", "-q", "-m", "Review snapshot")
        head = git("rev-parse", "HEAD")
        request = {
            "schema_version": rr.REQUEST_VERSION,
            "repository": "evaluation-snapshot/formal-conjectures",
            "head_commit": head,
            "merge_base": base,
            "scope": [case["path"]],
            "procedure": rr.descriptors(procedure),
            "sources": rr.descriptors(sources),
            "required_checks": ["build"],
        }
        request["id"] = rr.request_id(request)
        rr.write_directory(out / "request", procedure | sources | {"request.json": rr.encode(request)})
        rr.write_directory(out / "inputs", sources | context | {"candidate.lean": candidate})
        (out / "output").mkdir()
        container = "fc-review-" + job["id"]
        # Only allowlisted public bytes enter the container; no suite, labels, fix commits or host credentials.
        mounts = [
            "--mount",
            f"type=bind,src={out / 'inputs/candidate.lean'},dst=/workspace/{case['path']},readonly",
            "--mount",
            f"type=bind,src={out / 'output'},dst=/output",
        ]
        if sources:
            mounts += ["--mount", f"type=bind,src={out / 'inputs/sources'},dst=/sources,readonly"]
        if job["arm"] == "skill":
            mounts += ["--mount", f"type=bind,src={root / 'skill'},dst=/skill,readonly"]
        record = {"status": "environment_error"}
        try:
            docker(
                "run",
                "-d",
                "--name",
                container,
                "--network",
                "none",
                "--cap-drop",
                "ALL",
                "--security-opt",
                "no-new-privileges",
                "--pids-limit",
                "256",
                "--memory",
                "6g",
                "--cpus",
                "2",
                *mounts,
                manifest["image"],
            )
            for p in [repo / ".git", *(repo / ".git").rglob("*")]:
                p.chmod(0o777 if p.is_dir() else 0o666)
            docker("cp", str(repo / ".git"), container + ":/workspace/.git")
            docker("exec", container, "git", "config", "--global", "--add", "safe.directory", "/workspace")
            docker("exec", container, "git", "config", "status.showUntrackedFiles", "no")
            for name in context:
                docker("cp", str(out / "inputs" / name), container + ":/output/" + Path(name).name)
            server_args = [
                str(HERE / "review-eval/workspace_server.py"),
                "--container",
                container,
                "--output",
                str(out),
                "--module",
                case["module"],
                "--max-calls",
                str(manifest["max_calls"]),
            ]
            record = invoke_model(
                prompt(case, request, job["arm"], model),
                out / "model",
                model,
                manifest["timeout"],
                review_schema(request, manifest["max_calls"], context),
                server_args,
            )
            if record["status"] == "completed":
                review = read(out / "model/answer.json")
                rr.require(
                    review["reviewer"] == model
                    and review["context_policy"] == case["context_policy"]
                    and review["prior_reviews"] == list(context),
                    "changed review identity",
                )
                evidence = {
                    p.relative_to(out).as_posix(): p.read_bytes() for p in (out / "evidence").glob("*.json")
                } | context
                builds = [
                    read(p) for p in sorted((out / "evidence").glob("*.json")) if read(p)["kind"] == "build"
                ]
                checks = []
                if builds:
                    b = builds[-1]
                    status = (
                        "error"
                        if b["timed_out"] or b["exit_code"] in (None, 124, 125, 126, 127, 137)
                        else "pass" if b["exit_code"] == 0 else "fail"
                    )
                    refs = [
                        name
                        for name, data in evidence.items()
                        if name.startswith("evidence/tool-") and json.loads(data)["kind"] == "build"
                    ]
                    checks = [
                        {
                            "kind": "build",
                            "status": status,
                            "producer": "isolated workspace build tool",
                            "policy": "lake --wfail build " + case["module"],
                            "detail": "Original read-only candidate; tool receipt retained.",
                            "evidence": refs,
                        }
                    ]
                rr.write_directory(
                    out / "check-inputs",
                    evidence
                    | {
                        "checks.json": rr.encode(
                            {
                                "request_id": request["id"],
                                "artifacts": rr.descriptors(evidence),
                                "checks": checks,
                            }
                        )
                    },
                )
                rr.write_directory(
                    out / "report",
                    rr.assemble(
                        out / "request", out / "request", out / "model/answer.json", out / "check-inputs"
                    ),
                )
                record["report_status"] = "assembled"
        except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
            record["error"] = str(error)
            record.setdefault("report_status", "invalid")
        finally:
            subprocess.run(["docker", "rm", "-f", container], capture_output=True, check=False)
            write(out / "result.json", record)
    print(job["id"], record["status"], record.get("report_status", "not_run"), flush=True)


def run(root, model, workers):
    manifest = verify(root)
    rr.require(workers in (1, 2), "workers must be 1 or 2")
    run_config = root / "run-config.json"
    config = {"model": model, "reasoning_effort": "high"}
    if run_config.exists():
        rr.require(read(run_config) == config, "cannot mix reviewer models")
    else:
        write(run_config, config)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        list(pool.map(lambda j: run_one(root, manifest, j, model), manifest["jobs"]))


ASSESS = """Assess the anonymous mathematical review using the reference dossier and tool transcript.
The reference key is provisional; challenge it when warranted. A merged correction is supporting
provenance, not a proof that every other part is clean. Accept alternative valid findings and repairs.
Do not penalize wording or missing headings. Every judgement needs specific evidence.
Return JSON with gold_status (confirmed/disputed/insufficient), detected_defects (array of reference
ids), findings (one per actual finding: index, status supported/unsupported/unresolved, actionable
boolean, repair valid/invalid/not_checked/not_proposed, duplicate boolean, evidence string),
uncertainty appropriate/inappropriate/not_applicable, and comments (string). Distinguish a source
mismatch from a checked mathematical counterexample. An untested repair is not validated.
Finding indices are zero-based: assess each index from 0 through N-1 exactly once.
"""


def assessment_schema(count):
    def obj(fields):
        return {
            "type": "object",
            "properties": fields,
            "required": list(fields),
            "additionalProperties": False,
        }

    def enum(*values):
        return {"type": "string", "enum": list(values)}

    return obj(
        {
            "gold_status": enum("confirmed", "disputed", "insufficient"),
            "detected_defects": {"type": "array", "items": {"type": "string"}},
            "findings": {
                "type": "array",
                "minItems": count,
                "maxItems": count,
                "items": obj(
                    {
                        "index": {"type": "integer", "minimum": 0, "maximum": max(0, count - 1)},
                        "status": enum("supported", "unsupported", "unresolved"),
                        "actionable": {"type": "boolean"},
                        "repair": enum("valid", "invalid", "not_checked", "not_proposed"),
                        "duplicate": {"type": "boolean"},
                        "evidence": {"type": "string"},
                    }
                ),
            },
            "uncertainty": enum("appropriate", "inappropriate", "not_applicable"),
            "comments": {"type": "string"},
        }
    )


def validate_assessment(assessment, case, count):
    rr.require(
        set(assessment) == {"gold_status", "detected_defects", "findings", "uncertainty", "comments"},
        "invalid assessment fields",
    )
    rr.require(assessment["gold_status"] in ("confirmed", "disputed", "insufficient"), "invalid gold status")
    ids = {d["id"] for d in case["gold"]["defects"]}
    found = assessment["detected_defects"]
    rr.require(
        isinstance(found, list) and len(set(found)) == len(found) and set(found) <= ids,
        "invalid defect match",
    )
    findings = assessment["findings"]
    rr.require(
        len(findings) == count and sorted(f["index"] for f in findings) == list(range(count)),
        "missing finding assessment",
    )
    for f in findings:
        rr.require(
            set(f) == {"index", "status", "actionable", "repair", "duplicate", "evidence"},
            "invalid finding fields",
        )
        rr.require(
            type(f["index"]) is int and type(f["actionable"]) is bool and type(f["duplicate"]) is bool,
            "invalid finding types",
        )
        rr.require(
            f["status"] in ("supported", "unsupported", "unresolved")
            and f["repair"] in ("valid", "invalid", "not_checked", "not_proposed")
            and bool(f["evidence"].strip()),
            "unsupported assessment",
        )
    rr.require(
        assessment["uncertainty"] in ("appropriate", "inappropriate", "not_applicable")
        and isinstance(assessment["comments"], str),
        "invalid uncertainty",
    )


def assessment_packet(root, job):
    case = next(c for c in read(root / "suite.json")["cases"] if c["id"] == job["case"])
    out = root / "runs" / job["id"]
    review = read(out / "model/answer.json")
    anonymous = {k: v for k, v in review.items() if k not in ("reviewer", "request_id")}
    transcript = [read(p) for p in sorted((out / "evidence").glob("*.json"))]
    # Procedural reads may reveal treatment: label blinding is not perfect blinding.
    return case, {
        "prompt": case["prompt"],
        "review": anonymous,
        "reference": case["gold"],
        "candidate": asset(root / "private-assets", case["candidate"]).decode(),
        "sources": {k: asset(root / "private-assets", v).decode() for k, v in case["sources"].items()},
        "tool_transcript": transcript,
    }


def assess(root, model, output=None):
    manifest = verify(root, check_tooling=False)
    output = output or root / "assessments"
    config = {
        "review_manifest_sha256": sha((root / "manifest.json").read_bytes()),
        "assessor_sha256": sha(Path(__file__).read_bytes()),
        "model": model,
    }
    if output.exists():
        rr.require(
            (output / "config.json").exists() and read(output / "config.json") == config,
            "assessment protocol changed; choose a fresh --out directory",
        )
    else:
        output.mkdir(parents=True)
        write(output / "config.json", config)
        for name in ("review_eval.py", "review_report.py"):
            shutil.copyfile(HERE / name, output / name)
    for job in manifest["jobs"]:
        result = root / "runs" / job["id"] / "result.json"
        dest = output / job["id"]
        if dest.exists() or not result.exists() or read(result).get("report_status") != "assembled":
            continue
        case, packet = assessment_packet(root, job)
        record = invoke_model(
            ASSESS + encode(packet).decode(),
            dest,
            model,
            240,
            assessment_schema(len(packet["review"]["findings"])),
        )
        if record["status"] == "completed":
            try:
                assessment = read(dest / "answer.json")
                validate_assessment(assessment, case, len(packet["review"]["findings"]))
                write(dest / "assessment.json", assessment)
            except (ValueError, KeyError, TypeError) as error:
                write(dest / "invalid.json", {"error": str(error)})
        print("assessed", job["id"], record["status"], flush=True)


def summarize(root, assessments=None):
    manifest, suite = verify(root, check_tooling=False), read(root / "suite.json")
    summary_output = assessments / "summary.json" if assessments is not None else root / "summary.json"
    if assessments is not None:
        rr.require(
            read(assessments / "config.json")["review_manifest_sha256"]
            == sha((root / "manifest.json").read_bytes()),
            "assessment belongs to another review iteration",
        )
    assessments = assessments or root / "assessments"
    cases = {c["id"]: c for c in suite["cases"]}
    result = {
        "qualification": "Development observations; model assessments are not human accuracy labels.",
        "unique_cases": len({j["case"] for j in manifest["jobs"]}),
        "unique_families": len({j["family"] for j in manifest["jobs"]}),
        "arms": {},
        "runs": [],
    }
    for arm in ("skill", "baseline"):
        totals = {
            "scheduled": 0,
            "assembled": 0,
            "assessed": 0,
            "unresolved_keys": 0,
            "reference_defects": 0,
            "detected_defects": 0,
            "supported_findings": 0,
            "unsupported_findings": 0,
            "unresolved_findings": 0,
            "duplicates": 0,
            "clean_cases_with_false_alarms": 0,
            "assessed_clean_cases": 0,
            "valid_repairs": 0,
            "invalid_repairs": 0,
            "appropriate_uncertainty": 0,
            "wall_seconds": 0,
            "output_tokens": 0,
            "usage_unavailable_runs": 0,
        }
        for j in [j for j in manifest["jobs"] if j["arm"] == arm]:
            totals["scheduled"] += 1
            p = root / "runs" / j["id"] / "result.json"
            r = read(p) if p.exists() else {"status": "not_run"}
            totals["assembled"] += r.get("report_status") == "assembled"
            totals["wall_seconds"] += r.get("wall_seconds", 0)
            totals["output_tokens"] += sum(u.get("output_tokens", 0) for u in r.get("usage", []))
            totals["usage_unavailable_runs"] += r["status"] not in (
                "not_run",
                "environment_error",
            ) and not r.get("usage")
            row = j | {"status": r["status"], "report_status": r.get("report_status", "not_run")}
            a = assessments / j["id"] / "assessment.json"
            if a.exists():
                a = read(a)
                case = cases[j["case"]]
                validate_assessment(
                    a, case, len(read(root / "runs" / j["id"] / "model/answer.json")["findings"])
                )
                totals["assessed"] += 1
                totals["unresolved_keys"] += a["gold_status"] != "confirmed"
                if a["gold_status"] == "confirmed":
                    totals["reference_defects"] += len(case["gold"]["defects"])
                    totals["detected_defects"] += len(a["detected_defects"])
                    if case["kind"] == "clean":
                        totals["assessed_clean_cases"] += 1
                        totals["clean_cases_with_false_alarms"] += any(
                            f["status"] == "unsupported" for f in a["findings"]
                        )
                for f in a["findings"]:
                    totals[f["status"] + "_findings"] += 1
                    totals["duplicates"] += f["duplicate"]
                    if f["repair"] in ("valid", "invalid"):
                        totals[f["repair"] + "_repairs"] += 1
                totals["appropriate_uncertainty"] += a["uncertainty"] == "appropriate"
                row["assessment"] = a
            result["runs"].append(row)
        result["arms"][arm] = totals
    write(summary_output, result)
    return result


def key_packet(suite_path, output):
    suite = load_suite(suite_path)
    output.mkdir(parents=True, exist_ok=False)
    forms = []
    for case in suite["cases"]:
        packet = {
            "prompt": case["prompt"],
            "candidate": asset(suite_path.parent, case["candidate"]).decode(),
            "sources": {k: asset(suite_path.parent, v).decode() for k, v in case["sources"].items()},
            "prior_context": {
                k: asset(suite_path.parent, v).decode() for k, v in case.get("context", {}).items()
            },
        }
        write(output / (case["id"] + ".json"), packet)
        forms.append(
            {"id": case["id"], "reviewer": None, "defects": None, "evidence": None, "comments": None}
        )
    write(output / "adjudication.json", forms)
    write(output / "manifest.json", {"suite_sha256": sha(suite_path.read_bytes()), "files": files(output)})


def human_packet(root, output):
    m = verify(root, check_tooling=False)
    output.mkdir(parents=True, exist_ok=False)
    forms = []
    for job in m["jobs"]:
        p = root / "runs" / job["id"] / "report/report.json"
        if not p.exists():
            continue
        _case, packet = assessment_packet(root, job)
        # Omit provisional expected answers and model assessments for the first human pass.
        packet.pop("reference")
        write(output / (job["id"] + ".json"), packet)
        forms.append(
            {
                "id": job["id"],
                "reviewer": None,
                "minutes_spent": None,
                "missed_defects": None,
                "false_alarms": None,
                "would_use": None,
                "comments": None,
            }
        )
    write(output / "feedback.json", forms)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    f = subs.add_parser("freeze")
    for field in ("suite", "skill", "out"):
        f.add_argument("--" + field, type=Path, required=True)
    f.add_argument("--image", required=True)
    f.add_argument("--cases", nargs="*")
    f.add_argument("--repeats", type=int, default=1)
    f.add_argument("--timeout", type=int, default=420)
    f.add_argument("--max-calls", type=int, default=30)
    p = subs.add_parser("key-packet")
    p.add_argument("--suite", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    for name in ("run", "assess", "summarize", "human-packet"):
        p = subs.add_parser(name)
        p.add_argument("--root", type=Path, required=True)
        if name in ("run", "assess"):
            p.add_argument("--model", default="gpt-5.6-sol")
        if name == "run":
            p.add_argument("--workers", type=int, default=1)
        if name == "human-packet":
            p.add_argument("--out", type=Path, required=True)
        if name == "assess":
            p.add_argument("--out", type=Path)
        if name == "summarize":
            p.add_argument("--assessments", type=Path)
    a = parser.parse_args()
    if a.command == "freeze":
        freeze(a.suite, a.skill, a.out, a.image, a.cases, a.repeats, a.timeout, a.max_calls)
    elif a.command == "key-packet":
        key_packet(a.suite.resolve(), a.out.resolve())
    elif a.command == "run":
        run(a.root.resolve(), a.model, a.workers)
    elif a.command == "assess":
        assess(a.root.resolve(), a.model, a.out.resolve() if a.out else None)
    elif a.command == "human-packet":
        human_packet(a.root.resolve(), a.out)
    else:
        print(
            json.dumps(
                summarize(a.root.resolve(), a.assessments.resolve() if a.assessments else None), indent=2
            )
        )


if __name__ == "__main__":
    main()
