"""Optional Codex adapter for controlled evaluations; never imported by the toolkit."""
import importlib.metadata
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
import review_report as rr
from conjectures.review_schema import review_schema

def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_bytes(rr.encode(value))

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
            k: v for k, v in os.environ.items() if k not in ("CODEX_SESSION_ID", "CODEX_THREAD_ID", "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GH_TOKEN", "GITHUB_TOKEN")
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
        "model_identity_source": "explicit CLI model selection; provider alias resolution is not exposed",
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
