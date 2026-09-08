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

"""Prepare pinned review inputs and render supplied evidence as an advisory report.

This local pilot never executes Lean, models, submitted code or network requests.
It validates record shape, input identity and retained bytes, not the truth of a
producer's claims. See scripts/review-report/README.md for the input contracts.
"""

import argparse
import hashlib
import html
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from urllib.parse import quote

ANGLES = ("source-fidelity", "statement-soundness", "metadata-hygiene")
KINDS = ("build", "proof")
REQUEST_VERSION = "fc.review-pilot.request.v1"
REPORT_VERSION = "fc.review-pilot.report.v1"


class InputError(ValueError):
    """Invalid or inconsistent evidence; not a mathematical rejection."""


def require(condition, message):
    if not condition:
        raise InputError(message)


def obj(value, fields, label):
    require(type(value) is dict and set(value) == set(fields.split()),
            f"{label}: expected exactly {fields}")


def text(value, label):
    require(type(value) is str and bool(value.strip()), f"{label}: expected nonempty text")
    require(not any(ord(c) < 32 and c not in '\n\t' for c in value),
            f"{label}: control character")


def array(value, label):
    require(type(value) is list, f"{label}: expected array")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2,
                       allow_nan=False) + "\n").encode("utf-8")


def parse(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def invalid(value):
        raise InputError(f"invalid JSON constant: {value}")

    try:
        value = json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)
        encode(value)  # Reject unpaired surrogates before creating output.
        return value
    except (ValueError, UnicodeError) as error:
        raise InputError(str(error)) from error


def read_json(path):
    return parse(Path(path).read_bytes())


def relative(value):
    text(value, "path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in value
            and value == path.as_posix() and value != ".", f"unsafe path: {value}")
    return path


def read_artifact(root, name):
    path = Path(root)
    require(not path.is_symlink(), f"symlink artifact directory: {root}")
    for part in relative(name).parts:
        path = path / part
        require(not path.is_symlink(), f"symlink artifact: {name}")
    require(path.is_file(), f"missing artifact: {name}")
    return path.read_bytes()


def collect(root, prefix, exclude_evals=False):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), f"not a plain directory: {root}")
    result = {}
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root)
        if exclude_evals and "evals" in rel.parts:
            continue
        require(not path.is_symlink(), f"symlink input: {path}")
        if path.is_file():
            name = f"{prefix}/{rel.as_posix()}"
            relative(name)
            result[name] = path.read_bytes()
    return result


def descriptors(files):
    return [{"path": path, "sha256": digest(raw)} for path, raw in sorted(files.items())]


def validate_descriptors(items, label):
    array(items, label)
    paths = set()
    for item in items:
        obj(item, "path sha256", label)
        relative(item["path"])
        require(item["path"] not in paths, f"duplicate artifact: {item['path']}")
        paths.add(item["path"])
        require(type(item["sha256"]) is str and
                re.fullmatch(r"[0-9a-f]{64}", item["sha256"]), f"{label}: invalid digest")


def request_id(request):
    return digest(encode({k: v for k, v in request.items() if k != "id"}))


def validate_request(request):
    obj(request, "schema_version repository head_commit merge_base scope procedure sources required_checks id",
        "request")
    require(request["schema_version"] == REQUEST_VERSION, "unsupported request version")
    text(request["repository"], "repository")
    for key in ("head_commit", "merge_base"):
        require(type(request[key]) is str and re.fullmatch(r"[0-9a-f]{40}", request[key]),
                f"invalid {key}")
    array(request["scope"], "scope")
    require(bool(request["scope"]), "empty review scope")
    for path in request["scope"]:
        relative(path)
    require(len(request["scope"]) == len(set(request["scope"])), "duplicate scope path")
    for field in ("procedure", "sources"):
        validate_descriptors(request[field], field)
        require(all(d["path"].startswith(field + "/") for d in request[field]),
                f"{field}: wrong artifact prefix")
    require(any(d["path"] == "procedure/SKILL.md" for d in request["procedure"]),
            "procedure must contain SKILL.md")
    array(request["required_checks"], "required_checks")
    require(all(type(k) is str and k in KINDS for k in request["required_checks"]),
            "unsupported required check")
    require(len(set(request["required_checks"])) == len(request["required_checks"]),
            "duplicate required check")
    require("build" in request["required_checks"], "build must be a required check")
    require(request["id"] == request_id(request), "request digest mismatch")


def git(checkout, *args):
    return subprocess.run(["git", "-C", str(checkout), *args], check=True,
                          capture_output=True).stdout


def prepare(checkout, repository, base, skill, sources, checks):
    head = git(checkout, "rev-parse", "HEAD").decode().strip()
    merge_base = git(checkout, "merge-base", "--", base, head).decode().strip()
    scope = git(checkout, "diff", "--no-ext-diff", "--no-renames", "--name-only", "-z",
                merge_base, head, "--").decode().rstrip("\0").split("\0")
    procedure = collect(skill, "procedure", exclude_evals=True)
    source_files = collect(sources, "sources")
    request = {"schema_version": REQUEST_VERSION, "repository": repository,
               "head_commit": head, "merge_base": merge_base, "scope": sorted(scope),
               "procedure": descriptors(procedure), "sources": descriptors(source_files),
               "required_checks": sorted({"build", *checks})}
    request["id"] = request_id(request)
    validate_request(request)
    template = {"request_id": request["id"], "reviewer": "REPLACE with reviewer/model identity",
                "context_policy": "fresh", "prior_reviews": [],
                "reconciliations": [], "coverage": {angle: "incomplete" for angle in ANGLES},
                "findings": [], "questions": ["Review has not run."]}
    files = procedure | source_files | {"request.json": encode(request),
                                       "review-template.json": encode(template)}
    return files


def load_request(folder):
    request = read_json(Path(folder) / "request.json")
    validate_request(request)
    files = {}
    for item in request["procedure"] + request["sources"]:
        raw = read_artifact(folder, item["path"])
        require(digest(raw) == item["sha256"], f"digest mismatch: {item['path']}")
        files[item["path"]] = raw
    return request, files


def references(items, available, label):
    array(items, label)
    require(bool(items), f"{label}: evidence required")
    for name in items:
        require(type(name) is str and name in available, f"unknown evidence: {name}")


def validate_review(review, request, available):
    fields = "request_id reviewer context_policy prior_reviews coverage findings questions"
    # Optional additive field: earlier v1 producers remain valid.
    if type(review) is dict and "reconciliations" in review:
        fields += " reconciliations"
    obj(review, fields, "review")
    require(review["request_id"] == request["id"], "review belongs to another request")
    text(review["reviewer"], "reviewer")
    require(review["context_policy"] in ("fresh", "rereview"), "unknown context policy")
    array(review["prior_reviews"], "prior_reviews")
    if review["context_policy"] == "fresh":
        require(not review["prior_reviews"], "fresh review cannot carry prior reviews")
    else:
        references(review["prior_reviews"], available, "prior review evidence")
    reconciliations = review.get("reconciliations", [])
    array(reconciliations, "reconciliations")
    require(not reconciliations or review["context_policy"] == "rereview",
            "reconciliation requires rereview context")
    seen = set()
    for item in reconciliations:
        obj(item, "prior_evidence status reason evidence", "reconciliation")
        prior = item["prior_evidence"]
        require(type(prior) is str and prior in review["prior_reviews"],
                "reconciliation must reference retained prior review")
        require(prior not in seen, "duplicate reconciliation")
        seen.add(prior)
        require(item["status"] in ("retained", "corrected", "withdrawn"),
                "invalid reconciliation status")
        text(item["reason"], "reconciliation reason")
        references(item["evidence"], available, "reconciliation evidence")
    obj(review["coverage"], " ".join(ANGLES), "coverage")
    require(all(v in ("complete", "incomplete") for v in review["coverage"].values()),
            "invalid coverage state")
    if review["coverage"]["source-fidelity"] == "complete":
        require(bool(request["sources"]), "complete source review requires retained sources")
    array(review["findings"], "findings")
    for finding in review["findings"]:
        obj(finding, "angle file line severity message suggestion evidence", "finding")
        require(finding["angle"] in ANGLES, "unknown finding angle")
        require(finding["file"] in request["scope"], "finding outside review scope")
        require(type(finding["line"]) is int and finding["line"] >= 0, "invalid finding line")
        require(finding["severity"] in ("semantic", "nit"), "unknown severity")
        text(finding["message"], "finding message")
        text(finding["suggestion"], "finding suggestion")
        references(finding["evidence"], available, "finding evidence")
    array(review["questions"], "questions")
    for question in review["questions"]:
        text(question, "question")


def load_checks(manifest, request, folder):
    obj(manifest, "request_id artifacts checks", "evidence manifest")
    require(manifest["request_id"] == request["id"], "checks belong to another request")
    validate_descriptors(manifest["artifacts"], "check artifacts")
    files = {}
    for item in manifest["artifacts"]:
        require(item["path"].startswith("evidence/"), "check artifact needs evidence/ prefix")
        raw = read_artifact(folder, item["path"])
        require(digest(raw) == item["sha256"], f"digest mismatch: {item['path']}")
        files[item["path"]] = raw
    array(manifest["checks"], "checks")
    kinds = set()
    for check in manifest["checks"]:
        obj(check, "kind status producer policy detail evidence", "check")
        require(type(check["kind"]) is str and check["kind"] in KINDS, "unknown check kind")
        require(check["kind"] not in kinds, "duplicate check kind")
        kinds.add(check["kind"])
        require(check["status"] in ("pass", "fail", "error", "not_run"), "unknown check status")
        for key in ("producer", "policy", "detail"):
            text(check[key], key)
        if check["status"] in ("pass", "fail"):
            references(check["evidence"], files, "check evidence")
        else:
            array(check["evidence"], "check evidence")
            for name in check["evidence"]:
                require(type(name) is str and name in files, "unknown check evidence")
    return files


def escape(value):
    value = html.escape(value, quote=False).replace("\n", " ").replace("\t", " ")
    return re.sub(r"([\\`*_{}\[\]()#+.!|>~-])", r"\\\1", value).replace("@", "&#64;")


def render(report, observation):
    req, review = report["request"], report["review"]
    lines = ["# FC review", "", f"**Freshness:** {observation['freshness']}",
             f"**Semantic review:** {report['semantic_verdict']}",
             f"**Review completeness:** {observation['completeness']}", "",
             f"Reviewed commit: `{req['head_commit']}`",
             f"Request: `{req['id']}`", f"Reviewer: {escape(review['reviewer'])}", "",
             "Supplied evidence; producer claims are not independently authenticated by this tool.",
             "This report does not decide acceptance or establish source fidelity or proof correctness.", "",
             "| Check | Reported result | Policy |", "| --- | --- | --- |"]
    for check in report["checks"]:
        lines.append(f"| {check['kind']} | {check['status']} | {escape(check['policy'])} |")
    for finding in review["findings"]:
        lines += ["", f"- **{finding['severity']} / {finding['angle']}** — "
                  f"{escape(finding['file'])}:{finding['line']}: {escape(finding['message'])}",
                  f"  Suggestion: {escape(finding['suggestion'])}"]
    if review.get("reconciliations"):
        lines += ["", "Prior findings:", ""]
        for item in review["reconciliations"]:
            lines.append(f"- **{item['status']}** — {escape(item['prior_evidence'])}: "
                         f"{escape(item['reason'])}")
    gaps = list(report["gaps"])
    if observation["freshness"] == "STALE":
        gaps.insert(0, "Review inputs changed; the verdict below applies only to the reviewed request.")
    if gaps:
        lines += ["", "Unresolved checks and questions:", ""]
        lines += [f"- {escape(gap)}" for gap in gaps]
    lines += ["", "Evidence:", ""]
    for item in report["artifacts"]:
        # Percent-encode names instead of interpolating them as Markdown link syntax.
        lines.append(f"- [{escape(item['path'])}]({quote(item['path'], safe='/')}) "
                     f"(`{item['sha256']}`)")
    return "\n".join(lines) + "\n"


def assemble(request_dir, current_dir, review_path, evidence_dir):
    request, retained = load_request(request_dir)
    current, _ = load_request(current_dir)
    review = read_json(review_path)
    manifest = read_json(Path(evidence_dir) / "checks.json")
    retained |= load_checks(manifest, request, evidence_dir)
    validate_review(review, request, retained)
    checks = list(manifest["checks"])
    for kind in request["required_checks"]:
        if not any(c["kind"] == kind for c in checks):
            checks.append({"kind": kind, "status": "not_run", "producer": "none",
                           "policy": "not supplied", "detail": "Required check missing.", "evidence": []})
    checks.sort(key=lambda c: c["kind"])
    gaps = [f"{angle}: incomplete" for angle, state in review["coverage"].items()
            if state == "incomplete"] + review["questions"]
    gaps += [f"{c['kind']}: {c['status']} — {c['detail']}" for c in checks if c["status"] != "pass"]
    semantic = any(f["severity"] == "semantic" for f in review["findings"])
    verdict = ("NEEDS REVISION" if semantic else "INCOMPLETE" if gaps else
               "ACCEPT WITH NITS" if review["findings"] else "CLEAN")
    fresh = request["id"] == current["id"]
    report = {"schema_version": REPORT_VERSION, "authority_effect": "none",
              "assembler_sha256": digest(Path(__file__).read_bytes()),
              "request": request, "review": review,
              "checks": checks, "artifacts": descriptors(retained),
              "completeness": "complete" if not gaps else "incomplete",
              "semantic_verdict": verdict, "gaps": gaps}
    observation = {"schema_version": "fc.review-pilot.observation.v1",
                   "report_sha256": digest(encode(report)), "current_request_id": current["id"],
                   "freshness": "current" if fresh else "STALE",
                   "completeness": report["completeness"] if fresh else "incomplete"}
    files = retained | {"request.json": encode(request), "current-request.json": encode(current),
                        "review.json": encode(review), "checks.json": encode(manifest),
                        "report.json": encode(report), "observation.json": encode(observation),
                        "summary.md": render(report, observation).encode()}
    return files


def write_directory(output, files):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    for name, raw in files.items():
        path = output / relative(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--checkout", type=Path, required=True)
    prep.add_argument("--repository", required=True, help="Repository locator supplied by the operator")
    prep.add_argument("--base", required=True)
    prep.add_argument("--skill", type=Path, required=True)
    prep.add_argument("--sources", type=Path, required=True)
    prep.add_argument("--require", action="append", choices=KINDS, default=[])
    prep.add_argument("--out", type=Path, required=True)
    build = sub.add_parser("assemble")
    for name in ("request", "current", "review", "evidence", "out"):
        build.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            files = prepare(args.checkout, args.repository, args.base, args.skill, args.sources,
                            args.require or ["build"])
        else:
            files = assemble(args.request, args.current, args.review, args.evidence)
        write_directory(args.out, files)
    except (InputError, OSError, UnicodeError, subprocess.CalledProcessError) as error:
        print(f"review-report: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
