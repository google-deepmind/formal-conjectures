#!/usr/bin/env python3
"""Fail-closed metadata binding for committed Krein Arb certificate receipts.

This does NOT rerun Arb and does NOT elevate the mathematical claim. It binds
the already-committed certificate metadata to exact repository/head/blob
identities and rejects mutations of those anchors.

RH_PROVEN=false; authority_effect=NONE.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

SCHEMA = "aegis.rh.krein-certificate-receipt.v2"
CANONICALIZATION = "aegis-json-integral-float-v1"
HEAD = "163304475c6141d05c64ab773a5eb4fbf66addcc"
REPOSITORY = "Aegis-Omega/AEGIS-OMEGA"
VERIFIER_PATH = "research/rh/verify_krein_arb_v1.py"
VERIFIER_BLOB = "84453dbcbce67087fb46fbd63cdd7e1e9f88576a"
LP_GENERATOR_PATH = "research/rh/krein_lp_cutting_plane_v1.py"
LP_GENERATOR_BLOB = "ff3f12dd29d446af0559e31110020ff4f86725ef"

ANCHORS = {
    "L0.98": {
        "certificate_path": "research/rh/KREIN_ARB_CERTIFICATE_L0.98.json",
        "certificate_blob": "f08a3c7ec06918290dbc3c6c8d78ae84388b1e2d",
        "lp_path": "research/rh/krein_lp_L0.98.json",
        "lp_blob": "1a253779b1df1a0245b8a41956144d212597ae54",
        "L": 0.98,
        "L_exact": "2206763817411543/2251799813685248",
        "m_certified": "0.005",
        "hat_bound": 1_000_000.0,
        "delta_bound": 1_000_000.0,
        "span": 8.0,
        "zero_cell": "0.004",
        "tail_start": "3000",
        "cells": 12157,
        "zero_cell_lower_prefix": "0.0001304919734561549976760717572249348521273023860184687893630273",
        "tail_lower_prefix": "3.696148152628815205549060105016740468012357853104460327251282571556592625541",
    },
    "L1.0": {
        "certificate_path": "research/rh/KREIN_ARB_CERTIFICATE_L1.0.json",
        "certificate_blob": "5d5933d716179f3750ca41172f3347d1166c6150",
        "lp_path": "research/rh/krein_lp_L1.0.json",
        "lp_blob": "b44296a5864978e4cfdf4796213114acd26fbde5",
        "L": 1.0,
        "L_exact": "1/1",
        "m_certified": "0.0015",
        "hat_bound": 1_000_000.0,
        "delta_bound": 10_000_000.0,
        "span": 8.0,
        "zero_cell": "0.004",
        "tail_start": "3000",
        "cells": 12186,
        "zero_cell_lower_prefix": "0.0001247108245301879293338303183767709209453631999256551964851253",
        "tail_lower_prefix": "3.792104378370854040667093697334418867001409542121331641417870393823906828621",
    },
}


class ReceiptError(ValueError):
    pass


def canonical_sha256(obj: dict) -> str:
    """Hash sorted compact UTF-8 JSON, normalizing finite integral floats.

    v1 treats 1 and 1.0 alike, preserves booleans/strings, and rejects nonfinite
    numbers. Other floats use Python's JSON binary64 serialization. This is a
    receipt-specific scheme, NOT a claim of full RFC 8785/JCS conformance.
    """
    def normalize(value):
        if isinstance(value, float):
            if not math.isfinite(value):
                raise ReceiptError("nonfinite JSON number")
            return int(value) if value.is_integer() else value
        if isinstance(value, dict):
            if not all(isinstance(key, str) for key in value):
                raise ReceiptError("JSON object keys must be strings")
            return {key: normalize(item) for key, item in value.items()}
        if isinstance(value, list):
            return [normalize(item) for item in value]
        if value is None or isinstance(value, (str, int, bool)):
            return value
        raise ReceiptError("unsupported JSON value")

    data = json.dumps(normalize(obj), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def load_receipt(path: Path) -> dict:
    """Read the supplied artifact, rejecting duplicate keys and invalid numbers."""
    def unique_object(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise ReceiptError(f"duplicate JSON key: {key}")
            out[key] = value
        return out

    def invalid_constant(value):
        raise ReceiptError(f"nonfinite JSON number: {value}")

    try:
        result = json.loads(path.read_text(encoding="utf-8"),
                            object_pairs_hook=unique_object,
                            parse_constant=invalid_constant)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ReceiptError(f"cannot read receipt {path}: {exc}") from exc
    if not isinstance(result, dict):
        raise ReceiptError("receipt must be a JSON object")
    return result


def verify_git_bindings(receipt: dict, repo_root: Path) -> None:
    """Verify each path/blob in the actual anchored Git tree, without network I/O."""
    def git(*args):
        try:
            return subprocess.run(
                ["git", "--no-replace-objects", "-C", str(repo_root), *args],
                check=True, capture_output=True, text=True, timeout=10,
            ).stdout
        except (OSError, subprocess.SubprocessError) as exc:
            raise ReceiptError(f"cannot inspect anchored Git source: {exc}") from exc

    head = receipt["exact_head"]
    if git("cat-file", "-t", head).strip() != "commit":
        raise ReceiptError("exact_head is not a Git commit")
    references = [
        (receipt["certificate"]["path"], receipt["certificate"]["git_blob_sha"]),
        (receipt["lp_candidate"]["path"], receipt["lp_candidate"]["git_blob_sha"]),
        (receipt["lp_candidate"]["generator_path"],
         receipt["lp_candidate"]["generator_git_blob_sha"]),
        (receipt["verifier"]["path"], receipt["verifier"]["git_blob_sha"]),
    ]
    for path, blob in references:
        entry = git("ls-tree", "-z", head, "--", path)
        expected = {f"{mode} blob {blob}\t{path}\0" for mode in ("100644", "100755")}
        if entry not in expected:
            raise ReceiptError(f"path/blob is not in exact_head: {path}")
        if git("cat-file", "-t", blob).strip() != "blob":
            raise ReceiptError(f"referenced blob is unavailable: {path}")


def verify_hat_support(receipt: dict, repo_root: Path) -> None:
    """The frozen verifier trusts the LP's `uk`; the Lean consumer needs every hat
    support [u-w, u+w] outside (-L, L). Check it exactly on the anchored LP blob."""
    try:
        text = subprocess.run(
            ["git", "--no-replace-objects", "-C", str(repo_root), "cat-file", "blob",
             receipt["lp_candidate"]["git_blob_sha"]],
            check=True, capture_output=True, text=True, timeout=10,
        ).stdout
        lp = json.loads(text)
        L, w = Fraction(lp["L"]), Fraction(lp["w"])
        uk = [Fraction(u) for u in lp["uk"]]
        n_coef = len(lp["coef"])
    except (OSError, subprocess.SubprocessError, ValueError, TypeError, KeyError) as exc:
        raise ReceiptError(f"cannot read anchored LP payload: {exc}") from exc
    if L != Fraction(receipt["parameters"]["L_exact"]):
        raise ReceiptError("LP payload L differs from L_exact")
    if n_coef != len(uk) + 5:
        raise ReceiptError("LP payload must carry one coefficient per hat plus 5 delta columns")
    if w <= 0 or not uk or min(uk) - w < L:
        raise ReceiptError("hat support intersects (-L, L)")


def make_receipt(name: str) -> dict:
    if name not in ANCHORS:
        raise ReceiptError(f"unknown anchor {name}")
    a = ANCHORS[name]
    core = {
        "schema": SCHEMA,
        "canonicalization": CANONICALIZATION,
        "status": "BOUND_COMMITTED_CERTIFICATE_METADATA",
        "authority_effect": "NONE",
        "rh_proven": False,
        "repository": REPOSITORY,
        "exact_head": HEAD,
        "certificate": {
            "path": a["certificate_path"],
            "git_blob_sha": a["certificate_blob"],
            "upstream_schema": "aegis.rh.krein-arb-certificate.v1",
        },
        "lp_candidate": {
            "path": a["lp_path"],
            "git_blob_sha": a["lp_blob"],
            "generator_path": LP_GENERATOR_PATH,
            "generator_git_blob_sha": LP_GENERATOR_BLOB,
        },
        "verifier": {
            "path": VERIFIER_PATH,
            "git_blob_sha": VERIFIER_BLOB,
            "precision_bits": 256,
        },
        "parameters": {
            "L": a["L"],
            "L_exact": a["L_exact"],
            "m_certified": a["m_certified"],
            "hat_bound": a["hat_bound"],
            "delta_bound": a["delta_bound"],
            "span": a["span"],
            "zero_cell": a["zero_cell"],
            "tail_start": a["tail_start"],
        },
        "observed_committed_result": {
            "cells": a["cells"],
            "zero_cell_lower_prefix": a["zero_cell_lower_prefix"],
            "tail_lower_prefix": a["tail_lower_prefix"],
        },
        "limitations": [
            "metadata binding only; this file does not rerun Arb",
            "the Arb inequality is not Lean-kernel checked",
            "no width >= L claim",
            "no RH claim",
        ],
    }
    out = dict(core)
    out["binding_sha256"] = canonical_sha256(core)
    return out


def validate_receipt(receipt: dict, name: str) -> None:
    expected = make_receipt(name)
    if set(receipt) != set(expected):
        raise ReceiptError("top-level field set mismatch")
    if receipt.get("binding_sha256") != canonical_sha256(
        {k: v for k, v in receipt.items() if k != "binding_sha256"}
    ):
        raise ReceiptError("binding_sha256 mismatch")
    if receipt != expected:
        raise ReceiptError("receipt differs from exact committed anchor")
    if receipt["authority_effect"] != "NONE" or receipt["rh_proven"] is not False:
        raise ReceiptError("authority/RH boundary violated")


def run_falsifiers(name: str, base: dict | None = None) -> dict:
    if base is None:
        base = load_receipt(Path(__file__).with_name(f"KREIN_CERTIFICATE_RECEIPT_V2_{name}.json"))
    validate_receipt(base, name)
    mutations = {
        "wrong_head": ("exact_head", "0" * 40),
        "wrong_verifier_blob": ("verifier.git_blob_sha", "1" * 40),
        "wrong_lp_blob": ("lp_candidate.git_blob_sha", "2" * 40),
        "wrong_cell_count": (
            "observed_committed_result.cells",
            base["observed_committed_result"]["cells"] + 1,
        ),
        "authority_escalation": ("authority_effect", "WRITE"),
        "rh_escalation": ("rh_proven", True),
    }
    results = {}
    for label, (path, value) in mutations.items():
        bad = copy.deepcopy(base)
        cur = bad
        keys = path.split(".")
        for key in keys[:-1]:
            cur = cur[key]
        cur[keys[-1]] = value
        bad["binding_sha256"] = canonical_sha256(
            {k: v for k, v in bad.items() if k != "binding_sha256"}
        )
        try:
            validate_receipt(bad, name)
        except ReceiptError:
            results[label] = "PASS_REJECTED"
        else:
            results[label] = "FAIL_ACCEPTED"
    if any(v != "PASS_REJECTED" for v in results.values()):
        raise SystemExit(json.dumps(results, indent=2))
    return {
        "schema": "aegis.rh.krein-certificate-receipt-falsifiers.v2",
        "anchor": name,
        "status": "PASS",
        "authority_effect": "NONE",
        "rh_proven": False,
        "results": results,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("anchor", choices=sorted(ANCHORS))
    ap.add_argument("--receipt", type=Path, help="artifact to validate; defaults to committed receipt")
    ap.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2],
                    help="Git checkout containing the exact source commit")
    ap.add_argument("--generate", action="store_true", help="explicitly generate instead of reading")
    ap.add_argument("--out", type=Path)
    ap.add_argument("--falsify", action="store_true")
    args = ap.parse_args()
    if args.generate and (args.receipt or args.falsify):
        ap.error("--generate cannot be combined with --receipt or --falsify")
    source = args.receipt or Path(__file__).with_name(
        f"KREIN_CERTIFICATE_RECEIPT_V2_{args.anchor}.json")
    try:
        if not args.generate and args.out and args.out.resolve() == source.resolve():
            raise ReceiptError("validation must not overwrite its input artifact")
        receipt = make_receipt(args.anchor) if args.generate else load_receipt(source)
        validate_receipt(receipt, args.anchor)
        verify_git_bindings(receipt, args.repo_root)
        verify_hat_support(receipt, args.repo_root)
        payload = run_falsifiers(args.anchor, receipt) if args.falsify else receipt
        text = json.dumps(payload, indent=2, sort_keys=True, allow_nan=False)
        if args.out:
            args.out.write_text(text + "\n", encoding="utf-8")
        print(text)
    except (ReceiptError, OSError, UnicodeError) as exc:
        ap.exit(1, f"receipt validation failed: {exc}\n")


if __name__ == "__main__":
    main()
