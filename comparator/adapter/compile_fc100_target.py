#!/usr/bin/env python3
"""Compile every generated Challenge in one shared project at LeanEval pins.

Each generated workspace pins the same Lean toolchain and Mathlib revision,
so building them separately would build Mathlib once per workspace. This
arranges them as modules of one Lake project instead — Mathlib is fetched and
built once for the whole set — which is what makes a hundred-workspace target
audit affordable, and is the arrangement the audit on
`google-deepmind/formal-conjectures#4951` used.

Per workspace it copies `ChallengeDeps.lean` and `Challenge.lean` in as
`Deps_<id>.lean` and `Chal_<id>.lean`, rewriting the one import between them,
and builds each `Chal_<id>` target separately so a failure is attributed to
its workspace rather than to the batch. `sorry` warnings are the workspaces
working; only errors fail a target.

Usage:
  python3 compile_fc100_target.py WORKSPACES_DIR --project DIR
      [--report FILE] [--known-failures FILE]

With `--known-failures`, exit non-zero unless the failing workspaces are
exactly the recorded `target`-stage ones.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

from leaneval_interface import dump_json


def arrange_project(workspaces_dir, project_dir):
    """Lay out the shared project; returns `{workspace_id: module_name}`.

    Workspace ids are already identifiers (the importer slugs them), so the
    module names need no further encoding.
    """
    workspaces_dir = pathlib.Path(workspaces_dir)
    project_dir = pathlib.Path(project_dir)
    project_dir.mkdir(parents=True, exist_ok=True)
    workspaces = sorted(
        entry for entry in workspaces_dir.iterdir() if (entry / "Challenge.lean").is_file()
    )
    if not workspaces:
        raise SystemExit(f"no generated workspaces under {workspaces_dir}")

    toolchain = (workspaces[0] / "lean-toolchain").read_text(encoding="utf-8")
    mathlib = None
    modules = {}
    libs = []
    for workspace in workspaces:
        this_toolchain = (workspace / "lean-toolchain").read_text(encoding="utf-8")
        if this_toolchain != toolchain:
            raise SystemExit(
                f"{workspace.name} pins {this_toolchain.strip()}, but the set "
                f"started with {toolchain.strip()}; one project needs one pin"
            )
        lakefile = tomllib.loads(
            (workspace / "lakefile.toml").read_text(encoding="utf-8")
        )
        this_mathlib = next(
            requirement for requirement in lakefile["require"]
            if requirement["name"] == "mathlib"
        )
        if mathlib is None:
            mathlib = this_mathlib
        elif this_mathlib != mathlib:
            raise SystemExit(f"{workspace.name} pins a different Mathlib")

        challenge = (workspace / "Challenge.lean").read_text(encoding="utf-8")
        deps_path = workspace / "ChallengeDeps.lean"
        deps_module = f"Deps_{workspace.name}"
        challenge_module = f"Chal_{workspace.name}"
        if deps_path.is_file():
            (project_dir / f"{deps_module}.lean").write_text(
                deps_path.read_text(encoding="utf-8"), encoding="utf-8"
            )
            challenge = re.sub(
                r"^import ChallengeDeps$",
                f"import {deps_module}",
                challenge,
                flags=re.MULTILINE,
            )
            libs.append(deps_module)
        (project_dir / f"{challenge_module}.lean").write_text(
            challenge, encoding="utf-8"
        )
        libs.append(challenge_module)
        modules[workspace.name] = challenge_module

    (project_dir / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    lakefile = ['name = "fc100_target"', "", "[leanOptions]", "autoImplicit = false"]
    lakefile += [
        "",
        "[[require]]",
        'name = "mathlib"',
        f'git = "{mathlib["git"]}"',
        f'rev = "{mathlib["rev"]}"',
    ]
    for lib in libs:
        lakefile += ["", "[[lean_lib]]", f'name = "{lib}"']
    (project_dir / "lakefile.toml").write_text(
        "\n".join(lakefile) + "\n", encoding="utf-8"
    )
    return modules


def build(project_dir, modules):
    """Build each Challenge target, attributing failures per workspace."""
    project_dir = pathlib.Path(project_dir)
    for command in (["lake", "update"], ["lake", "exe", "cache", "get"]):
        completed = subprocess.run(command, cwd=project_dir)
        if completed.returncode != 0:
            raise SystemExit(f"{' '.join(command)} failed in {project_dir}")
    results = []
    for workspace_id, module in sorted(modules.items()):
        completed = subprocess.run(
            ["lake", "build", module],
            cwd=project_dir,
            capture_output=True,
            text=True,
        )
        errors = [
            line
            for line in (completed.stdout + completed.stderr).splitlines()
            if "error:" in line
        ]
        ok = completed.returncode == 0 and not errors
        results.append(
            {
                "workspace": workspace_id,
                "status": "ok" if ok else "target-failed",
                **({} if ok else {"reason": "\n".join(errors[:10]) or "build failed"}),
            }
        )
        print(f"{workspace_id}: {'ok' if ok else 'FAILED'}", flush=True)
    return results


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("workspaces", help="directory of generated workspaces")
    ap.add_argument("--project", required=True, help="shared project directory")
    ap.add_argument("--report", default=None, help="write the JSON report here")
    ap.add_argument(
        "--known-failures",
        default=None,
        help="fail unless failing workspaces are exactly the recorded target ones",
    )
    args = ap.parse_args(argv)

    modules = arrange_project(args.workspaces, args.project)
    results = build(args.project, modules)
    failed = {entry["workspace"] for entry in results if entry["status"] != "ok"}
    report = {
        "total": len(results),
        "ok": len(results) - len(failed),
        "failed": sorted(failed),
        "results": results,
    }
    if args.report:
        pathlib.Path(args.report).write_text(
            dump_json(report), encoding="utf-8"
        )
    print(f"{report['ok']}/{report['total']} Challenges compile at target pins")

    if args.known_failures:
        with open(args.known_failures, "rb") as handle:
            recorded = tomllib.load(handle)
        # Known failures are recorded by declaration; workspaces are named by
        # the slugged id, which the `workspace` field of each entry supplies.
        expected = {
            entry["workspace"]
            for entry in recorded.get("failure", [])
            if entry.get("stage") == "target" and "workspace" in entry
        }
        unexpected = sorted(failed - expected)
        fixed = sorted(expected - failed)
        for name in unexpected:
            print(f"unexpected target failure: {name}", file=sys.stderr)
        for name in fixed:
            print(
                f"{name} is recorded as a known target failure but compiled; "
                "remove it from the record",
                file=sys.stderr,
            )
        if unexpected or fixed:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
