#!/usr/bin/env python3
"""Export a pinned FC declaration to a package-backed generator v2 workspace."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SOURCE_REPOSITORY = "https://github.com/google-deepmind/formal-conjectures.git"


def run(args, cwd=ROOT, **kwargs):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=600, **kwargs)
    if result.returncode:
        raise RuntimeError(f"{' '.join(map(str, args))}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def module_name(path):
    # Quote complete path components: a filename may itself contain a dot.
    parts = path.with_suffix("").parts
    if any("»" in part or "\n" in part for part in parts):
        raise ValueError("Unsupported module path")
    return ".".join(f"«{part}»" for part in parts)


def source_pin(reference):
    revision = run(["git", "rev-parse", reference]).strip()
    paths = ["FormalConjectures", "FormalConjecturesForMathlib", "FormalConjecturesUtil",
             "FormalConjecturesUtil.lean", "FormalConjecturesForMathlib.lean",
             "lean-toolchain", "lake-manifest.json"]
    run(["git", "diff", "--exit-code", revision, "--", *paths])
    if run(["git", "ls-files", "--others", "--exclude-standard", "--", *paths]).strip():
        raise ValueError("Untracked source cannot be part of a pinned export")
    pinned = tomllib.loads(run(["git", "show", f"{revision}:lakefile.toml"]))
    observed = tomllib.loads((ROOT / "lakefile.toml").read_text())
    for key in ("name", "require", "leanOptions", "lean_lib"):
        if pinned.get(key) != observed.get(key):
            raise ValueError(f"Lake configuration {key} differs from the source snapshot")
    return revision


def render_module(module, exported):
    text = f"import {module}\n\n"
    levels = list(dict.fromkeys(level for d in exported["declarations"] for level in d["levels"]))
    if levels:
        text += "universe " + " ".join(levels) + "\n\n"
    holes = []
    for declaration in exported["declarations"]:
        start_line = text.count("\n") + 1
        kind = declaration["kind"]
        command = "noncomputable def" if kind == "def" else "theorem"
        block = f"{command} {declaration['name']} : {declaration['type']} := by\n  sorry"
        holes.append({"declarationName": declaration["name"], "module": "FCExportedProblem",
                      "startLine": start_line, "startColumn": 0,
                      "endLine": start_line + block.count("\n"), "endColumn": 7,
                      "kind": kind, "explicitParameters": [],
                      "sameModuleDependencies": [], "holeDependentDependencies": []})
        text += block + "\n\n"
    return text, holes


def response_files(response, problem_id):
    if set(response) != {"schemaVersion", "files"} or response["schemaVersion"] != 2:
        raise ValueError("Unexpected generator response")
    files = {}
    for entry in response["files"]:
        if set(entry) != {"problemId", "path", "content", "sha256"}:
            raise ValueError("Unexpected generator file record")
        path = entry["path"]
        if (entry["problemId"] != problem_id or not path or "\\" in path or "\x00" in path
                or ":" in path or PurePosixPath(path).is_absolute()
                or any(part in ("", ".", "..") for part in path.split("/"))
                or path in files or path == "fc-provenance.json"):
            raise ValueError(f"Invalid workspace path or identity: {path!r}")
        if digest(entry["content"]) != entry["sha256"]:
            raise ValueError(f"Generator digest mismatch: {path}")
        files[path] = entry["content"]
    if not {"Challenge.lean", "Solution.lean", "Submission.lean", "lakefile.toml", "config.json"} <= files.keys():
        raise ValueError("Incomplete workspace")
    return files


def export(source, declaration, out, generator, source_ref="origin/main",
           source_repository=SOURCE_REPOSITORY):
    source = source.resolve()
    relative = source.relative_to(ROOT)
    revision = source_pin(source_ref)
    source_text = run(["git", "show", f"{revision}:{relative.as_posix()}"])
    if source_text != source.read_text():
        raise ValueError("Source differs from its pinned commit")
    module = module_name(relative)
    generator = generator.resolve()
    generator_revision = run(["git", "rev-parse", "HEAD"], cwd=generator).strip()
    run(["git", "diff", "--exit-code", "HEAD"], cwd=generator)
    # Build the checkout we record rather than trusting an arbitrary binary on PATH.
    run(["lake", "--wfail", "build"], cwd=generator)
    run(["lake", "--wfail", "build", "export_problem", module])
    exported = json.loads(run(["lake", "env", ".lake/build/bin/export_problem",
                               str(relative), module, declaration]))
    text, holes = render_module(module, exported)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    toolchain = (ROOT / "lean-toolchain").read_text()
    problem_id = "fc_" + digest(module + ":" + declaration)[:16]
    out = out.resolve()
    if out.exists():
        raise ValueError(f"Output already exists: {out}")
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".fc-export-", dir=out.parent) as temporary:
        staging = Path(temporary)
        context = staging / "context"
        context.mkdir()
        rendered = context / "FCExportedProblem.lean"
        rendered.write_text(text)
        metadata = context / ".lake/build/lib/lean/FCExportedProblem.ilean"
        metadata.parent.mkdir(parents=True)
        # Real Lean-generated metadata; no emulation of the .ilean format.
        run(["lake", "env", "lean", "-i", str(metadata), str(rendered)])
        request = {"schemaVersion": 2, "contextRoot": "context", "leanToolchain": toolchain,
                   "mathlib": {"name": "mathlib", "git": mathlib["url"], "rev": mathlib["rev"]},
                   "dependencies": [{"name": "formal_conjectures", "git": source_repository,
                                     "rev": revision}],
                   "templates": {"workspaceTest": (ROOT / "comparator/WorkspaceTest.lean").read_text()},
                   "problems": [{"id": problem_id, "title": declaration,
                                 "group": ("open-conjectures" if exported["category"] == "research open"
                                           else "formalization-evaluation"), "status": "draft", "visible": False,
                                 "statementRevision": 1, "tags": [exported["category"]] if exported["category"] else [],
                                 "submitter": "Formal Conjectures",
                                 "moduleName": "FCExportedProblem", "moduleContent": text,
                                 "holes": [h["declarationName"] for h in holes], "resolvedHoles": holes}]}
        request_text = json.dumps(request, indent=2) + "\n"
        files = response_files(json.loads(run([str(generator / ".lake/build/bin/lean-eval-generator")],
                                              cwd=staging, input=request_text)), problem_id)
        provenance = {"schemaVersion": 1, "source": {"repository": source_repository,
                      "commit": revision, "path": relative.as_posix(), "module": module,
                      "declaration": declaration, "sha256": digest(source_text)},
                      "generatorCommit": generator_revision, "requestSha256": digest(request_text),
                      "files": {path: digest(content) for path, content in files.items()}}
        workspace = staging / "workspace"
        for path, content in files.items():
            destination = workspace / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content)
        (workspace / "fc-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        (staging / "request.json").write_text(request_text)
        (staging / "export.json").write_text(json.dumps(exported, indent=2) + "\n")
        staging.rename(out)
    return out / "workspace"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("declaration")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--generator", type=Path, required=True, help="Clean generator v2 Git checkout")
    parser.add_argument("--source-ref", default="origin/main", help="Exact source snapshot (default: origin/main)")
    parser.add_argument("--source-repository", default=SOURCE_REPOSITORY)
    args = parser.parse_args()
    try:
        print(export(args.source, args.declaration, args.out, args.generator,
                     args.source_ref, args.source_repository))
    except (RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
