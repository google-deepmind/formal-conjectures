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
REVIEW_TOOLS = ("review_eval.py", "review_report.py", "review-eval/workspace_server.py")


encode = rr.encode
sha = rr.digest
read = rr.read_json


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(encode(value))


def asset(root, name):
    # Resolve the caller's root once (macOS /tmp is an ancestor symlink), then
    # apply the same path and symlink checks as production report evidence.
    return rr.read_artifact(Path(root).resolve(), name)


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
    for relative in REVIEW_TOOLS:
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
            "tooling": {p.name: sha(p.read_bytes()) for p in (HERE / name for name in REVIEW_TOOLS)},
        },
    )


def verify(root, *, check_tooling=True):
    m = read(root / "manifest.json")
    if check_tooling:
        for p in (HERE / name for name in REVIEW_TOOLS):
            rr.require(sha(p.read_bytes()) == m["tooling"][p.name], "tooling changed since freeze")
    for name, digest in m["frozen_files"].items():
        rr.require(sha(asset(root, name)) == digest, "frozen inputs changed")
    return m


def docker(*args, **kwargs):
    return subprocess.run(["docker", *args], check=True, capture_output=True, **kwargs)


def schema_object(**fields):
    return {"type": "object", "properties": fields, "required": list(fields), "additionalProperties": False}


def schema_array(item, **limits):
    return {"type": "array", "items": item, **limits}


def schema_enum(*values):
    return {"type": "string", "enum": list(values)}


STRING = {"type": "string"}
BOOLEAN = {"type": "boolean"}


def review_schema(request, max_calls=30, context=()):
    paths = [item["path"] for item in request.get("sources", [])]
    paths += [f"evidence/tool-{n:03d}.json" for n in range(1, max_calls + 1)]
    evidence = schema_array(schema_enum(*paths, *context), minItems=1)
    return schema_object(
        request_id=schema_enum(request["id"]),
        reviewer=STRING,
        context_policy=schema_enum("fresh", "rereview"),
        prior_reviews=schema_array(STRING),
        coverage=schema_object(**{angle: schema_enum("complete", "incomplete") for angle in rr.ANGLES}),
        findings=schema_array(
            schema_object(
                angle=schema_enum(*rr.ANGLES),
                file=schema_enum(*request["scope"]),
                line={"type": "integer", "minimum": 0},
                severity=schema_enum("semantic", "nit"),
                message=STRING,
                suggestion=STRING,
                evidence=evidence,
            )
        ),
        questions=schema_array(STRING),
        reconciliations=schema_array(
            schema_object(
                prior_evidence=schema_enum(*context) if context else STRING,
                status=schema_enum("retained", "corrected", "withdrawn"),
                reason=STRING,
                evidence=evidence,
            ),
            **({} if context else {"maxItems": 0}),
        ),
    )


def prompt(case, request, arm, model):
    # The shared prompt specifies task, environment and transport only, not review strategy.
    text = (
        case["prompt"] + "\n\nThe workspace is an isolated evaluation checkout at /workspace. "
        "The original file is read-only. Use the workspace tools; scratch files go in /output. "
        "Read AGENTS.md and the ordinary contribution guidance. Available source snapshots are "
        "in /sources; networking is disabled equally for both conditions. "
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
        "--json",
        "-o",
        str(destination / "answer.json"),
    ]
    settings = {"model_reasoning_effort": '"high"', "web_search": '"disabled"'}
    for feature in (
        "shell_tool",
        "unified_exec",
        "multi_agent",
        "apps",
        "plugins",
        "remote_plugin",
        "browser_use",
        "in_app_browser",
        "skill_search",
    ):
        settings["features." + feature] = "false"
    # --ignore-user-config alone still discovers host skill catalogs.
    installed = {
        str(p.parent)
        for folder in (".codex/skills", ".agents/skills", ".codex/plugins/cache")
        for p in (Path.home() / folder).rglob("SKILL.md")
    }
    overrides = ",".join("{path=" + json.dumps(p) + ",enabled=false}" for p in sorted(installed))
    settings["skills.config"] = "[" + overrides + "]"
    if schema:
        write(destination / "schema.json", schema)
        args += ["--output-schema", str(destination / "schema.json")]
    if server_args:
        server = {
            "command": json.dumps(sys.executable),
            "args": json.dumps(server_args),
            "default_tools_approval_mode": '"approve"',
            "required": "true",
            "tool_timeout_sec": "90",
        }
        settings.update(
            {"mcp_servers.review_workspace." + key: value for key, value in server.items()}
        )
    for key, value in settings.items():
        args += ["-c", f"{key}={value}"]
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
        engine_env = {
            k: v for k, v in os.environ.items() if k not in ("CODEX_SESSION_ID", "CODEX_THREAD_ID")
        }
        engine_env["CODEX_HOME"] = str(engine_directory)
        with (
            (destination / "events.jsonl").open("w") as out,
            (destination / "stderr.txt").open("w") as err,
        ):
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


def snapshot(repo, path, candidate):
    """Create the same read-only Git history for both arms; upstream provenance stays separate."""
    target = repo / path
    target.parent.mkdir(parents=True)
    target.write_bytes(candidate)
    env = os.environ | {
        "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
        "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
    }

    def git(*args):
        command = [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "commit.gpgSign=false",
            "-C",
            str(repo),
            *args,
        ]
        return subprocess.check_output(command, env=env, stderr=subprocess.DEVNULL).decode().strip()

    git("init", "-q")
    for key, value in (
        ("user.name", "Evaluation"),
        ("user.email", "eval@localhost"),
        ("status.showUntrackedFiles", "no"),
    ):
        git("config", key, value)
    git("commit", "-q", "--allow-empty", "-m", "Base")
    base = git("rev-parse", "HEAD")
    git("branch", "origin/main")
    git("add", ".")
    git("commit", "-q", "-m", "Review snapshot")
    head = git("rev-parse", "HEAD")
    for entry in [repo / ".git", *(repo / ".git").rglob("*")]:
        entry.chmod(0o755 if entry.is_dir() else 0o644)
    return head, base


def build_checks(evidence, module, binding):
    # Parse the native receipts once. Generic command output never becomes a build verdict.
    receipts = {
        name: rr.parse(raw) for name, raw in evidence.items() if name.startswith("evidence/tool-")
    }
    builds = {name: receipt for name, receipt in receipts.items() if receipt["kind"] == "build"}
    if not builds:
        return []
    for receipt in builds.values():
        rr.require(
            receipt.get("environment") == binding,
            "build environment does not match request",
        )
        rr.require(
            receipt.get("command")
            == ["timeout", "-k", "2", "60", "lake", "--wfail", "build", module],
            "build command does not match request",
        )
    latest = next(reversed(builds.values()))
    failed_to_run = latest["timed_out"] or latest["exit_code"] in (
        None,
        124,
        125,
        126,
        127,
        137,
    )
    status = "error" if failed_to_run else "pass" if latest["exit_code"] == 0 else "fail"
    return [
        {
            "kind": "build",
            "status": status,
            "producer": "isolated workspace build tool",
            "policy": "lake --wfail build " + module,
            "detail": "Original candidate built in a fresh pinned container; no reviewer scratch state.",
            "evidence": list(builds),
        }
    ]


def assemble_run(out, case, request, context, model):
    review = read(out / "model/answer.json")
    rr.require(
        review["reviewer"] == model
        and review["context_policy"] == case["context_policy"]
        and review["prior_reviews"] == list(context),
        "changed review identity",
    )
    evidence = rr.collect(out / "evidence", "evidence") | context
    environment = read(out / "request/context/environment.json")
    binding = {
        "isolation": "fresh_container",
        "image": environment["image"],
        "module": case["module"],
        "candidate_path": case["path"],
        "candidate_sha256": sha((out / "request/context/candidate.lean").read_bytes()),
    }
    checks = {
        "request_id": request["id"],
        "artifacts": rr.descriptors(evidence),
        "checks": build_checks(evidence, case["module"], binding),
    }
    rr.write_directory(out / "check-inputs", evidence | {"checks.json": encode(checks)})
    rr.write_directory(
        out / "report",
        rr.assemble(
            out / "request",
            out / "request",
            out / "model/answer.json",
            out / "check-inputs",
        ),
    )


def run_one(root, manifest, job, model):
    out = root / "runs" / job["id"]
    if out.exists():
        return  # Never overwrite or silently retry an existing attempt.
    out.mkdir(parents=True)
    container, record = "fc-review-" + job["id"], {"status": "environment_error"}
    try:
        case = next(c for c in read(root / "suite.json")["cases"] if c["id"] == job["case"])
        sources = {
            "sources/" + name: asset(root / "private-assets", path)
            for name, path in case["sources"].items()
        }
        context = {
            name: asset(root / "private-assets", path)
            for name, path in case.get("context", {}).items()
        }
        procedure = review_procedure(root / "skill", job["arm"])
        candidate = asset(root / "private-assets", case["candidate"])
        with tempfile.TemporaryDirectory(prefix="fc-review-snapshot-") as temp:
            repo = Path(temp)
            head, base = snapshot(repo, case["path"], candidate)
            snapshot_context = {
                "context/candidate.lean": candidate,
                "context/environment.json": encode(
                    {
                        "image": manifest["image"],
                        "environment_commit": read(root / "suite.json")["environment_commit"],
                        "tooling": manifest["tooling"],
                        "limitation": "Replay requires the pinned evaluation image; source is retained.",
                    }
                ),
            }
            request = {
                "schema_version": rr.REQUEST_VERSION,
                "repository": "evaluation-snapshot/formal-conjectures",
                "head_commit": head,
                "merge_base": base,
                "base_tip": base,
                "context": rr.descriptors(snapshot_context),
                "scope": [case["path"]],
                "procedure": rr.descriptors(procedure),
                "sources": rr.descriptors(sources),
                "required_checks": ["build"],
            }
            request["id"] = rr.request_id(request)
            rr.write_directory(
                out / "request",
                procedure | sources | snapshot_context | {"request.json": encode(request)},
            )
            rr.write_directory(out / "inputs", sources | context | {"candidate.lean": candidate})
            (out / "output").mkdir()
            (out / "evidence").mkdir()
            # Mount only public inputs. The suite, labels, fix commits and credentials stay on the host.
            mounts = {
                out / "inputs/candidate.lean": f"/workspace/{case['path']},readonly",
                out / "output": "/output",
            }
            if sources:
                mounts[out / "inputs/sources"] = "/sources,readonly"
            if job["arm"] == "skill":
                mounts[root / "skill"] = "/skill,readonly"
            mount_args = [
                f"--mount=type=bind,src={source},dst={target}" for source, target in mounts.items()
            ]
            docker(
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
                *mount_args,
                manifest["image"],
            )
            docker("cp", str(repo / ".git"), container + ":/workspace/.git")
            docker(
                "exec",
                container,
                "git",
                "config",
                "--global",
                "--add",
                "safe.directory",
                "/workspace",
            )
            for name in context:
                docker(
                    "cp",
                    str(out / "inputs" / name),
                    container + ":/output/" + Path(name).name,
                )
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
                "--image",
                manifest["image"],
                "--candidate",
                str(out / "inputs/candidate.lean"),
                "--candidate-path",
                case["path"],
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
                assemble_run(out, case, request, context, model)
                record["report_status"] = "assembled"
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        record.update(error=str(error), report_status="invalid")
    finally:
        subprocess.run(
            ["docker", "rm", "-f", container + "-build"],
            capture_output=True,
            check=False,
        )
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
Also judge verdict_calibration and rereview_handling (appropriate/inappropriate/not_applicable)
with separate evidence strings. An unresolved semantic finding that forces NEEDS REVISION
is not appropriate merely because missing source coverage is disclosed. Judge severity as
well as whether an observation is true. A rereview must justify retaining, correcting or
withdrawing the prior claim; do not infer success from an empty findings list.
"""


def assessment_schema(count):
    return schema_object(
        gold_status=schema_enum("confirmed", "disputed", "insufficient"),
        detected_defects=schema_array(STRING),
        findings=schema_array(
            schema_object(
                index={"type": "integer", "minimum": 0, "maximum": max(0, count - 1)},
                status=schema_enum("supported", "unsupported", "unresolved"),
                actionable=BOOLEAN,
                repair=schema_enum("valid", "invalid", "not_checked", "not_proposed"),
                duplicate=BOOLEAN,
                evidence=STRING,
            ),
            minItems=count,
            maxItems=count,
        ),
        uncertainty=schema_enum("appropriate", "inappropriate", "not_applicable"),
        verdict_calibration=schema_enum("appropriate", "inappropriate", "not_applicable"),
        verdict_evidence=STRING,
        rereview_handling=schema_enum("appropriate", "inappropriate", "not_applicable"),
        rereview_evidence=STRING,
        comments=STRING,
    )


def validate_assessment(assessment, case, count):
    # Old assessment sets remain readable; new calls always request calibrated verdicts.
    extra = " verdict_calibration verdict_evidence rereview_handling rereview_evidence"
    calibrated = "verdict_calibration" in assessment
    rr.obj(
        assessment,
        "gold_status detected_defects findings uncertainty comments" + (extra if calibrated else ""),
        "assessment",
    )
    if calibrated:
        for field in ("verdict_calibration", "rereview_handling"):
            rr.require(
                assessment[field] in ("appropriate", "inappropriate", "not_applicable"),
                "invalid calibration judgement",
            )
        for field in ("verdict_evidence", "rereview_evidence"):
            rr.text(assessment[field], field)
    rr.require(assessment["gold_status"] in ("confirmed", "disputed", "insufficient"), "invalid gold status")
    found = assessment["detected_defects"]
    rr.array(found, "detected defects")
    rr.require(all(type(item) is str for item in found), "invalid defect id")
    rr.require(
        len(set(found)) == len(found) and set(found) <= {d["id"] for d in case["gold"]["defects"]},
        "invalid defect match",
    )
    findings = assessment["findings"]
    rr.array(findings, "findings")
    for finding in findings:
        rr.obj(finding, "index status actionable repair duplicate evidence", "finding assessment")
        rr.require(
            type(finding["index"]) is int
            and type(finding["actionable"]) is bool
            and type(finding["duplicate"]) is bool,
            "invalid finding types",
        )
        rr.require(
            finding["status"] in ("supported", "unsupported", "unresolved")
            and finding["repair"] in ("valid", "invalid", "not_checked", "not_proposed"),
            "invalid finding judgement",
        )
        rr.text(finding["evidence"], "assessment evidence")
    rr.require(sorted(f["index"] for f in findings) == list(range(count)), "missing finding assessment")
    rr.require(
        assessment["uncertainty"] in ("appropriate", "inappropriate", "not_applicable"), "invalid uncertainty"
    )
    rr.require(isinstance(assessment["comments"], str), "invalid comments")


def case_packet(assets, case):
    """Public case contents only; shared by model assessment and blind human adjudication."""
    return {
        "prompt": case["prompt"],
        "candidate": asset(assets, case["candidate"]).decode(),
        "sources": {name: asset(assets, path).decode() for name, path in case["sources"].items()},
        "prior_context": {
            name: asset(assets, path).decode() for name, path in case.get("context", {}).items()
        },
    }


def assessment_packet(root, job):
    case = next(c for c in read(root / "suite.json")["cases"] if c["id"] == job["case"])
    out = root / "runs" / job["id"]
    review = read(out / "model/answer.json")
    # Procedural reads may reveal treatment: label blinding is not perfect blinding.
    packet = case_packet(root / "private-assets", case) | {
        "review": {k: v for k, v in review.items() if k not in ("reviewer", "request_id")},
        "reference": case["gold"],
        "report_outcome": {
            k: read(out / "report/report.json")[k] for k in ("semantic_verdict", "completeness", "gaps")
        },
        "tool_transcript": [read(p) for p in sorted((out / "evidence").glob("*.json"))],
    }
    return case, packet


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
            "verdict_calibration": {
                k: 0 for k in ("appropriate", "inappropriate", "not_applicable", "ungraded")
            },
            "rereview_handling": {
                k: 0 for k in ("appropriate", "inappropriate", "not_applicable", "ungraded")
            },
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
                for field in ("verdict_calibration", "rereview_handling"):
                    totals[field][a.get(field, "ungraded")] += 1
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
        write(output / (case["id"] + ".json"), case_packet(suite_path.parent, case))
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
