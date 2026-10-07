#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed local module import/order audit for the Krein RH replay step."""

from __future__ import annotations
import argparse
from pathlib import Path
import re
import sys

STEP = "- name: Compile and audit certified approximation and spectral obstruction"
NEXT_STEP = "- name: Upload Krein bridge replay logs"
GROUP = re.compile(r"(?m)^\s*for m in ([A-Za-z0-9_ ]+); do\s*$")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(.+)$")
MODULE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


def prebuilt_root_verified(workflow: str, name: str) -> bool:
    """Trust only the named root module built in the earlier exact workflow step."""
    if name != "RHKreinCriticalLineBridgeV1":
        return False
    before = workflow.split(STEP, 1)[0]
    return (
        f"cp AEGISOverlay/{name}.lean {name}.lean" in before
        and f"lake env lean -o .lake/build/lib/lean/{name}.olean {name}.lean" in before
    )


def compile_plan(workflow: str) -> list[tuple[str, str]]:
    if workflow.count(STEP) != 1 or workflow.count(NEXT_STEP) != 1:
        raise ValueError("compile-step anchors not unique")
    block = workflow.split(STEP, 1)[1].split(NEXT_STEP, 1)[0]
    groups = GROUP.findall(block)
    if len(groups) != 2:
        raise ValueError(f"expected overlay and root compile loops, found {len(groups)}")
    names = [[s for s in group.split() if s] for group in groups]
    if any(not group or any(not MODULE.fullmatch(m) for m in group) for group in names):
        raise ValueError("invalid module list")
    plan = [("AEGISOverlay", m) for m in names[0]] + [("root", m) for m in names[1]]
    modules = [m for _, m in plan]
    if len(set(modules)) != len(modules):
        raise ValueError("duplicate compiled module")
    return plan


def audit(root: Path, workflow: str) -> tuple[list[str], int]:
    plan = compile_plan(workflow)
    where = {name: (group, i) for i, (group, name) in enumerate(plan)}
    problems: list[str] = []
    imports_checked = 0
    for group, name in plan:
        source = root / "AEGISOverlay" / f"{name}.lean"
        if not source.is_file():
            problems.append(f"{name}: missing declared source {source}")
            continue
        for line in source.read_text(encoding="utf-8").splitlines():
            code = line.split("--", 1)[0].strip()
            m = IMPORT.fullmatch(code)
            if not m:
                continue
            for target in m.group(1).split():
                if target.startswith("AEGISOverlay."):
                    dep = target[len("AEGISOverlay."):]
                    required_group = "AEGISOverlay"
                else:
                    dep = target
                    required_group = "root"
                local_path = root / "AEGISOverlay" / f"{dep}.lean"
                if dep not in where:
                    if (required_group == "root" and local_path.is_file()
                            and prebuilt_root_verified(workflow, dep)):
                        imports_checked += 1
                        continue
                    if (required_group == "AEGISOverlay" or local_path.is_file()) and local_path.is_file():
                        problems.append(f"{name}: local import {target} omitted from compile plan")
                    elif required_group == "AEGISOverlay":
                        problems.append(f"{name}: unresolved local overlay import {target}")
                    continue
                imports_checked += 1
                dep_group, dep_index = where[dep]
                if dep_group != required_group:
                    problems.append(f"{name}: import {target} expects {dep_group} module, not {required_group}")
                if dep_index >= where[name][1]:
                    problems.append(f"{name}: import {target} built after its consumer")
    return problems, imports_checked


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=Path("."))
    p.add_argument("--workflow", type=Path,
                   default=Path(".github/workflows/rh-snowflake-log23-globalization-v1.yml"))
    args = p.parse_args(argv)
    try:
        problems, n = audit(args.root, (args.root / args.workflow).read_text(encoding="utf-8"))
    except (OSError, ValueError) as ex:
        print(f"RH_IMPORT_GRAPH=FAIL ({ex})")
        return 1
    if problems:
        print("RH_IMPORT_GRAPH=FAIL")
        print("\n".join(problems))
        return 1
    print(f"RH_IMPORT_GRAPH=PASS LOCAL_IMPORT_EDGES={n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
