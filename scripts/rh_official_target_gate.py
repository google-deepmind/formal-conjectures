#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed acceptance classifier for the official RH theorem."""

from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

OFFICIAL = "FormalConjectures/Millennium/RiemannHypothesis.lean"
GOAL = "AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10"
WINDOW_GOAL_PATTERN = re.compile(
    r"^∀\s+(?:\(L\s*:\s*ℝ\)|L\s*:\s*ℝ),\s*"
    r"(?:693\s*/\s*2000|\(693\s*/\s*2000\s*:\s*ℝ\))\s*<\s*L\s*→\s*"
    r"(?:AEGIS\.WeilWindowExhaustionV1\.)?WindowArithmeticNonpositiveV1\s+L$"
)
THEOREM = "RiemannHypothesis.riemannHypothesis"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
LEAN_ERROR = re.compile(r"(?m)^(?:[^\n]*?:\d+:\d+:\s*)?error(?:\([^)]*\))?:\s*([^\n]+)$")
LEAN_GOAL = re.compile(r"(?m)^⊢\s*(\S[^\n]*)$")
AXIOMS = re.compile(r"'RiemannHypothesis\.riemannHypothesis' depends on axioms:\s*\[([^]]*)\]", re.S)
AXIOM_FREE = re.compile(r"'RiemannHypothesis\.riemannHypothesis' does not depend on any axioms")

def rh_body(source: str) -> str | None:
    dec = re.search(r"(?m)^theorem\s+riemannHypothesis\s*:\s*RiemannHypothesis\s*:=\s*by\s*$", source)
    if dec is None:
        return None
    rest = source[dec.end():]
    end = re.search(r"(?m)^end\s+RiemannHypothesis\s*$", rest)
    return rest[:end.start()] if end else None

def classify(source: str, log: str, lean_exit: int, axioms_log: str | None = None) -> tuple[str, list[str]]:
    body = rh_body(source)
    if body is None or re.search(r"\b(?:sorry|sorryAx|admit|axiom)\b", body):
        return "TARGET_SOURCE_INVALID", []
    errors = LEAN_ERROR.findall(log)
    goals = LEAN_GOAL.findall(log)
    if lean_exit != 0:
        if errors == ["unsolved goals"] and goals == [GOAL]:
            return "OPEN_UNIVERSAL_ZERO_QUADRATIC", errors
        if (errors == ["unsolved goals"] and len(goals) == 1
                and WINDOW_GOAL_PATTERN.fullmatch(goals[0])
                and "import RHSmallWindowCanonicalJoinV1" in source
                and "apply AEGIS.RHSmallWindowCanonicalJoinV1.riemannHypothesis_of_above_693_over_2000_v1" in body):
            return "OPEN_PROVED_WINDOW_COMPLEMENT", errors
        return "COMPILER_FAILURE_UNEXPECTED", errors
    if errors or goals or "sorryAx" in log:
        return "COMPILER_OUTPUT_INVALID", errors
    if axioms_log is None:
        return "COMPILED_AWAITING_AXIOM_AUDIT", []
    if re.search(r"(?m)^.*\berror(?:\([^)]*\))?:", axioms_log) or "sorryAx" in axioms_log:
        return "AXIOM_AUDIT_FAILED", []
    match = AXIOMS.search(axioms_log)
    if match is None:
        return ("FORMAL_RH_CLOSED", []) if AXIOM_FREE.search(axioms_log) else ("AXIOM_AUDIT_MISSING", [])
    axioms = {t.strip() for t in match.group(1).split(",") if t.strip()}
    if not axioms.issubset(ALLOWED_AXIOMS):
        return "AXIOM_AUDIT_FAILED", []
    return "FORMAL_RH_CLOSED", []

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--log", type=Path, required=True)
    p.add_argument("--lean-exit", type=int, required=True)
    p.add_argument("--receipt", type=Path, required=True)
    p.add_argument("--axioms-log", type=Path)
    args = p.parse_args(argv)
    if not args.source.as_posix().endswith(OFFICIAL):
        p.error("--source must be the actual official RH file")
    original = args.source.read_bytes()
    log = args.log.read_text(encoding="utf-8")
    ax = args.axioms_log.read_text(encoding="utf-8") if args.axioms_log else None
    status, errors = classify(original.decode("utf-8"), log, args.lean_exit, ax)
    receipt = {
        "schema": "aegis.rh.official-target-gate.v1",
        "target": THEOREM,
        "file": OFFICIAL,
        "head_sha": os.environ.get("RH_EXACT_HEAD", "UNVERIFIED"),
        "source_sha256": hashlib.sha256(original).hexdigest(),
        "lean_exit_code": args.lean_exit,
        "compiler_errors": errors,
        "expected_residual": (
            GOAL if status == "OPEN_UNIVERSAL_ZERO_QUADRATIC" else
            "WINDOW_SIGN_FOR_ALL_L_GT_693_OVER_2000"
            if status == "OPEN_PROVED_WINDOW_COMPLEMENT" else None
        ),
        "disposition": status,
        "rh_proven_unconditionally": status == "FORMAL_RH_CLOSED",
    }
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"RH_TARGET_DISPOSITION={status}")
    print(f"RH_TARGET_RECEIPT={args.receipt}")
    return 0 if status in {"COMPILED_AWAITING_AXIOM_AUDIT", "FORMAL_RH_CLOSED"} else 1

if __name__ == "__main__":
    sys.exit(main())
