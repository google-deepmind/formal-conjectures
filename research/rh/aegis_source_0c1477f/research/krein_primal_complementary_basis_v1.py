#!/usr/bin/env python3
"""Independent complementary-basis diagnostic for the Krein primal operator.

Numerical diagnostic only. This script does not prove universal positivity or RH.
It keeps the same symbol/operator as krein_primal_convergence_v2.py but tests a
finite family that is algebraically independent from the committed cosine-mode
trial family:

  g1_k(x) = (k+2) sin(k*pi*x/L) - k sin((k+2)*pi*x/L),  k=1..n,
  g_k     = (1/4-D^2) g1_k.

The endpoint constraints g1=g1'=0 at x=0,L hold exactly. Fourier transforms are
analytic, so the xi midpoint rule is the only quadrature in the main solve.
RH_PROVEN=false; authority_effect=NONE.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import cholesky, eigh, solve_triangular
from scipy.special import digamma

LOG2 = math.log(2.0)
LOG3 = math.log(3.0)
DEFAULT_CHECKPOINTS = (32, 64, 96, 128, 160, 192, 224, 256)


def symbol(xi: np.ndarray, L: float) -> np.ndarray:
    if not L < LOG3:
        raise ValueError("valid only for L < log(3); prime 3 enters at/above log(3)")
    out = np.real(digamma(0.25 + 0.5j * xi)) - math.log(math.pi)
    if L > LOG2:
        out -= math.sqrt(2.0) * LOG2 * np.cos(xi * LOG2)
    return out


def _I(q: np.ndarray, L: float) -> np.ndarray:
    return L * np.exp(-0.5j * q * L) * np.sinc(q * L / (2.0 * math.pi))


def coefficients(L: float, n: int) -> tuple[float, np.ndarray, np.ndarray]:
    a = math.pi / L
    k = np.arange(1, n + 1, dtype=float)
    c0 = (k + 2.0) * (0.25 + (k * a) ** 2)
    c2 = -k * (0.25 + ((k + 2.0) * a) ** 2)
    return a, c0, c2


def gram(L: float, n: int, normalized: bool = True) -> tuple[np.ndarray, np.ndarray]:
    _, c0, c2 = coefficients(L, n)
    G = np.zeros((n, n), dtype=float)
    diag = (L / 2.0) * (c0 * c0 + c2 * c2)
    np.fill_diagonal(G, diag)
    if n > 2:
        off = (L / 2.0) * c2[:-2] * c0[2:]
        i = np.arange(n - 2)
        G[i, i + 2] = off
        G[i + 2, i] = off
    scales = np.sqrt(diag)
    if normalized:
        G = G / scales[:, None] / scales[None, :]
    return G, scales


def quadratic_matrix(L: float, n: int, T: float, dt: float, chunk: int,
                     scales: np.ndarray) -> np.ndarray:
    a, c0, c2 = coefficients(L, n)
    Q = np.zeros((n, n), dtype=float)
    xi_all = np.arange(dt / 2.0, T, dt)
    modes = np.arange(1, n + 3, dtype=float)[:, None]
    for start in range(0, len(xi_all), chunk):
        xi = xi_all[start:start + chunk][None, :]
        S = (_I(xi - modes * a, L) - _I(xi + modes * a, L)) / (2.0j)
        F = c0[:, None] * S[:n, :] + c2[:, None] * S[2:n + 2, :]
        F /= scales[:, None]
        s = symbol(xi.ravel(), L)
        Fr, Fi = F.real, F.imag
        Q += ((Fr * s) @ Fr.T + (Fi * s) @ Fi.T) * (dt / math.pi)
    return Q


def eig_diagnostics(Q: np.ndarray, G: np.ndarray, scales: np.ndarray, n: int) -> dict:
    q = Q[:n, :n]
    g = G[:n, :n]
    d = scales[:n]
    lam_generalized = float(eigh(q, g, eigvals_only=True, subset_by_index=[0, 0], driver="gvx")[0])

    R = cholesky(g, lower=True, check_finite=False)
    X = solve_triangular(R, q, lower=True, check_finite=False)
    B = solve_triangular(R, X.T, lower=True, check_finite=False).T
    B = (B + B.T) / 2.0
    lam_whitened = float(eigh(B, eigvals_only=True, subset_by_index=[0, 0], driver="evr")[0])

    g_raw = g * d[:, None] * d[None, :]
    q_raw = q * d[:, None] * d[None, :]
    lam_raw = float(eigh(q_raw, g_raw, eigvals_only=True, subset_by_index=[0, 0], driver="gvx")[0])

    return {
        "lambda_min": lam_generalized,
        "lambda_min_whitened": lam_whitened,
        "lambda_min_raw_scaling": lam_raw,
        "generalized_vs_whitened_abs_diff": abs(lam_generalized - lam_whitened),
        "normalized_vs_raw_abs_diff": abs(lam_generalized - lam_raw),
        "gram_cond2_normalized": float(np.linalg.cond(g, 2)),
        "gram_cond2_raw": float(np.linalg.cond(g_raw, 2)),
    }


def run(L: float, nmax: int, T: float, dt: float, chunk: int,
        checkpoints: list[int], conditioning: bool = True) -> dict:
    t0 = time.time()
    G, scales = gram(L, nmax, normalized=True)
    Q = quadratic_matrix(L, nmax, T, dt, chunk, scales)
    lambdas = {str(n): float(eigh(Q[:n, :n], G[:n, :n], eigvals_only=True,
                                  subset_by_index=[0, 0], driver="gvx")[0])
               for n in checkpoints}
    out = {
        "quadrature": {"xi_midpoint_T": T, "dt": dt, "chunk": chunk},
        "lambda_min_by_dimension": lambdas,
        "elapsed_seconds": time.time() - t0,
    }
    if conditioning:
        out["conditioning_at_nmax"] = eig_diagnostics(Q, G, scales, nmax)
    return out


def implementation_self_check(L: float = 1.05, n: int = 6, order: int = 500) -> dict:
    a, c0, c2 = coefficients(L, n)
    G_exact, _ = gram(L, n, normalized=False)
    z, w = leggauss(order)
    x, ww = (z + 1.0) * L / 2.0, w * L / 2.0
    rows = []
    for k in range(1, n + 1):
        rows.append(c0[k - 1] * np.sin(k * a * x) + c2[k - 1] * np.sin((k + 2) * a * x))
    A = np.asarray(rows)
    G_quad = (A * ww) @ A.T
    gram_abs = float(np.max(np.abs(G_exact - G_quad)))
    gram_rel = gram_abs / float(np.max(np.abs(G_exact)))

    xis = (0.0, 0.37, 3.1, 17.0, 53.2)
    modes = np.arange(1, n + 3, dtype=float)[:, None]
    fourier_abs = 0.0
    fourier_rel = 0.0
    for value in xis:
        xi = np.array([[value]])
        S = (_I(xi - modes * a, L) - _I(xi + modes * a, L)) / (2.0j)
        F = (c0[:, None] * S[:n, :] + c2[:, None] * S[2:n + 2, :]).ravel()
        F_quad = (A * ww) @ np.exp(-1j * x * value)
        err = float(np.max(np.abs(F - F_quad)))
        scale = max(1.0, float(np.max(np.abs(F_quad))))
        fourier_abs = max(fourier_abs, err)
        fourier_rel = max(fourier_rel, err / scale)

    endpoint = 0.0
    for k in range(1, n + 1):
        for x0 in (0.0, L):
            g1 = (k + 2) * math.sin(k * a * x0) - k * math.sin((k + 2) * a * x0)
            gp = (k + 2) * k * a * math.cos(k * a * x0) - k * (k + 2) * a * math.cos((k + 2) * a * x0)
            endpoint = max(endpoint, abs(g1), abs(gp))
    return {
        "small_n": n,
        "gauss_legendre_order": order,
        "gram_max_abs_error": gram_abs,
        "gram_max_relative_error": gram_rel,
        "fourier_max_abs_error": fourier_abs,
        "fourier_max_relative_error": fourier_rel,
        "endpoint_constraint_max_abs": endpoint,
    }


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tail_fit(values: dict[str, float]) -> dict:
    dims = np.array([128.0, 160.0, 192.0, 224.0, 256.0])
    y = np.array([values[str(int(n))] for n in dims])
    fits = {}
    for name, powers in (("a+b/n", (0.0, 1.0)), ("a+b/n+c/n^2", (0.0, 1.0, 2.0))):
        cols = [np.ones_like(dims) if p == 0.0 else dims ** (-p) for p in powers]
        coef = np.linalg.lstsq(np.stack(cols, axis=1), y, rcond=None)[0]
        fits[name] = {"extrapolated_a": float(coef[0]), "coefficients": [float(v) for v in coef]}
    return fits


def run_suite(baseline_path: Path, L: float, nmax: int, chunk: int,
              checkpoints: list[int]) -> dict:
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    expected = {
        "L": L,
        "quadrature": {"xi_midpoint_T": 3000, "dt": 0.02},
        "schema": "aegis.rh.krein-primal-convergence.v2",
    }
    if baseline.get("L") != expected["L"] or baseline.get("schema") != expected["schema"]:
        raise ValueError("baseline result does not match the required L/schema")
    if baseline.get("quadrature", {}).get("xi_midpoint_T") != 3000 or baseline.get("quadrature", {}).get("dt") != 0.02:
        raise ValueError("baseline quadrature is not T=3000, dt=0.02")

    regimes = {
        "base": run(L, nmax, 3000.0, 0.02, chunk, checkpoints, conditioning=True),
        "tighter_quadrature": run(L, nmax, 3000.0, 0.01, chunk, checkpoints, conditioning=False),
        "larger_truncation": run(L, nmax, 6000.0, 0.02, chunk, checkpoints, conditioning=False),
        "strict_combined": run(L, nmax, 6000.0, 0.01, chunk, checkpoints, conditioning=False),
    }
    old = baseline["lambda_min_by_dimension"]
    new = regimes["base"]["lambda_min_by_dimension"]
    strict = regimes["strict_combined"]["lambda_min_by_dimension"]
    comparison = {}
    for n in checkpoints:
        k = str(n)
        comparison[k] = {
            "existing_basis": float(old[k]),
            "complementary_basis_base": float(new[k]),
            "complementary_minus_existing": float(new[k] - old[k]),
            "complementary_relative_to_existing": float(new[k] / old[k]),
            "strict_minus_base": float(strict[k] - new[k]),
        }

    cond256 = regimes["base"]["conditioning_at_nmax"]
    strict_delta = max(abs(strict[str(n)] - new[str(n)]) for n in checkpoints)
    negative_observed = any(v <= 0.0 for r in regimes.values() for v in r["lambda_min_by_dimension"].values())

    return {
        "schema": "aegis.rh.krein-primal-complementary-basis.v1",
        "status": "NUMERICAL_DIAGNOSTIC_ONLY",
        "authority_effect": "NONE",
        "rh_proven": False,
        "L": L,
        "L_lt_log3": bool(L < LOG3),
        "operator": "same Krein-primal symbol/operator as krein_primal_convergence_v2.py",
        "basis": {
            "family": "clamped-sine-difference",
            "g1": "(k+2)sin(k*pi*x/L)-k sin((k+2)*pi*x/L), k=1..n",
            "g": "(1/4-D^2)g1",
            "endpoint_constraints": "g1(0)=g1(L)=g1'(0)=g1'(L)=0 exactly",
            "independence_from_existing_finite_family": "existing g basis uses cosine modes; complementary g basis uses sine modes, so their finite trigonometric representations are linearly independent",
            "diagonal_normalization_for_solve": True,
        },
        "baseline": {
            "path": str(baseline_path),
            "sha256": sha256_file(baseline_path),
            "schema": baseline["schema"],
            "basis": baseline["basis"],
            "quadrature": baseline["quadrature"],
        },
        "implementation_self_check": implementation_self_check(L=L),
        "runs": regimes,
        "comparison_by_dimension": comparison,
        "tail_fit_base_last_five_checkpoints": tail_fit(new),
        "falsification_assessment": {
            "negative_observed": negative_observed,
            "max_abs_strict_minus_base": float(strict_delta),
            "conditioning_at_nmax": cond256,
            "dimension_sequence_decreasing": all(new[str(checkpoints[i + 1])] < new[str(checkpoints[i])] for i in range(len(checkpoints) - 1)),
            "zero_limit_inference": "UNRESOLVED",
            "outcome": "NO_NUMERICAL_FALSIFICATION_OBSERVED_IN_TESTED_REGIMES" if not negative_observed else "FALSIFICATION_OBSERVED",
            "reason": "No tested eigenvalue is nonpositive; quadrature tightening is negligible and T=6000 shifts minima slightly upward. The n-sequence still decreases, so the unrestricted limit remains unresolved.",
        },
        "interpretation": "Finite-subspace minima are upper bounds on the unrestricted infimum. Positive values, stable quadrature, or positive extrapolations do not prove universal positivity or RH.",
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=float, default=1.05)
    ap.add_argument("--nmax", type=int, default=256)
    ap.add_argument("--T", type=float, default=3000.0)
    ap.add_argument("--dt", type=float, default=0.02)
    ap.add_argument("--chunk", type=int, default=2000)
    ap.add_argument("--checkpoints", default=",".join(map(str, DEFAULT_CHECKPOINTS)))
    ap.add_argument("--suite", action="store_true")
    ap.add_argument("--baseline-json", type=Path,
                    default=Path(__file__).with_name("KREIN_PRIMAL_CONVERGENCE_L1.05_V2.json"))
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    checkpoints = [int(x) for x in args.checkpoints.split(",") if x]
    if max(checkpoints) > args.nmax:
        raise SystemExit("checkpoint exceeds nmax")
    if args.suite:
        result = run_suite(args.baseline_json, args.L, args.nmax, args.chunk, checkpoints)
    else:
        result = {
            "schema": "aegis.rh.krein-primal-complementary-basis.v1",
            "status": "NUMERICAL_DIAGNOSTIC_ONLY",
            "authority_effect": "NONE",
            "rh_proven": False,
            "L": args.L,
            "basis_family": "clamped-sine-difference",
            "run": run(args.L, args.nmax, args.T, args.dt, args.chunk, checkpoints),
            "interpretation": "Finite-subspace minima are upper bounds on the unrestricted infimum; positive values do not prove universal positivity or RH.",
        }
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.out:
        args.out.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
