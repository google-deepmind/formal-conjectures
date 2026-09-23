"""Optional hosted API adapter; not part of the installed contribution toolkit."""
import json
import os
import time
import urllib.request
from pathlib import Path
import review_report as rr
from conjectures import execution as ex
from conjectures.review_schema import review_schema
MAX_CALLS = 20
MAX_SECONDS = 420

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(rr.encode(value))

def model_review(request, container, evidence, model):
    history = [
        {
            "role": "user",
            "content": "Review the scoped FC contribution. Read /tmp/work/procedure/SKILL.md and follow it. "
            "Use execute for reads and optional scratch checks in /tmp/work. No network is available. "
            "The source snapshot is not authoritative source evidence: unavailable cited sources "
            "must leave source-fidelity coverage incomplete. This is a fresh advisory review. "
            "The independent build receipt is supplied separately; never claim proof verification. "
            "Stop after resolving material questions; do not repeat completed checks. "
            "Return the review JSON. Evidence paths are evidence/tool-NNN.json from tool results. "
            + json.dumps({"request_id": request["id"], "scope": request["scope"], "reviewer": model}),
        }
    ]
    started = time.monotonic()
    calls = 0
    usage = []
    while calls <= MAX_CALLS:
        remaining = MAX_SECONDS - (time.monotonic() - started)
        rr.require(remaining > 0, "model time budget exhausted")
        body = {
            "model": model,
            "store": False,
            "input": history,
            "reasoning": {"effort": "high"},
            "max_output_tokens": 8000,
            "text": {
                "format": {
                    "type": "json_schema",
                    "name": "fc_review",
                    "strict": True,
                    "schema": review_schema(request, MAX_CALLS),
                }
            },
            "tools": [
                {
                    "type": "function",
                    "name": "execute",
                    "description": "Run a bounded command in the isolated review scratch copy.",
                    "strict": True,
                    "parameters": {
                        "type": "object",
                        "properties": {"command": {"type": "string"}},
                        "required": ["command"],
                        "additionalProperties": False,
                    },
                }
            ],
            "parallel_tool_calls": False,
        }
        req = urllib.request.Request(
            "https://api.openai.com/v1/responses",
            data=rr.encode(body),
            headers={
                "Authorization": "Bearer " + os.environ["OPENAI_API_KEY"],
                "Content-Type": "application/json",
            },
        )
        with urllib.request.urlopen(req, timeout=min(remaining, 180)) as response:
            value = json.load(response)
        write(evidence / f"model-response-{len(usage):03d}.json", value)
        usage.append(value.get("usage"))
        rr.require(value.get("status") == "completed", "model response incomplete")
        history.extend(value["output"])
        tools = [item for item in value["output"] if item["type"] == "function_call"]
        if not tools:
            texts = [
                part["text"]
                for item in value["output"]
                if item["type"] == "message"
                for part in item["content"]
                if part["type"] == "output_text"
            ]
            review = json.loads("".join(texts))
            rr.require(
                review["context_policy"] == "fresh" and not review["prior_reviews"],
                "pilot requires a fresh review",
            )
            review["reviewer"] = value.get("model", model)
            return review
        for item in tools:
            calls += 1
            rr.require(calls <= MAX_CALLS and item["name"] == "execute", "invalid tool or exhausted budget")
            command = json.loads(item["arguments"])["command"]
            remaining = int(MAX_SECONDS - (time.monotonic() - started))
            rr.require(remaining > 0, "model time budget exhausted")
            record = ex.execute(container, ["sh", "-c", command], min(60, remaining))
            name = f"evidence/tool-{calls:03d}.json"
            write(evidence / Path(name).name, record)
            history.append(
                {
                    "type": "function_call_output",
                    "call_id": item["call_id"],
                    "output": json.dumps({"evidence": name, **record}),
                }
            )
    raise ValueError("model tool budget exhausted")
