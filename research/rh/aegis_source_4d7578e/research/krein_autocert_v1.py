"""Self-calibrating Krein certificate pipeline (v1).

    python3 krein_autocert_v1.py L OUTDIR

No tuning constant is chosen by hand:
  1. primal margin m*(L) (B-spline Rayleigh quotient)          -> upper bound for any certificate margin
  2. LP ladder over (span, hat bound, delta bound)            -> first rung with positive LP margin
  3. m_cert = FRACTION * min_xi F_0(xi)/W(xi) on a fine grid   -> F_0 = W S + Hhat (margin-free)
  4. Arb via krein_arb_receipt_v2.py                           -> on failure: zero-cell failure halves the
     zero cell, interior failure scales m_cert by BACKOFF; bounded retries
  5. OUTDIR/calibration_L<L>.json records every rung/attempt; the Arb receipt is the only source of numbers.
    python3 krein_autocert_v1.py table OUTDIR   -> markdown table generated from receipts (for RH_STATUS.md)
"""
import json, math, os, subprocess, sys
from fractions import Fraction
import numpy as np
from scipy.interpolate import BSpline
from scipy.linalg import eigh
from scipy.optimize import linprog
from scipy.special import psi

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import krein_dual_beyond_log2 as K

LADDER = [(4, 1e5, 1e6), (8, 1e5, 1e6), (8, 1e6, 1e6), (8, 1e6, 1e7), (12, 1e6, 1e7), (16, 1e6, 1e7)]
FRACTION, BACKOFF, MAX_TRIES = 0.8, 0.6, 4
W_HAT, XI_MAX, DXI, FINE = 0.02, 300.0, 0.01, 0.0002


def primal_margin(L, nb=40, deg=7, T=400.0, dt=0.01, M=4000):
    kn = np.concatenate([[0] * deg, np.linspace(0, L, nb - deg + 1), [L] * deg])
    x = np.linspace(0, L, M + 1); wx = np.full(M + 1, L / M); wx[0] = wx[-1] = L / M / 2
    B = np.array([BSpline(kn, np.eye(len(kn) - deg - 1)[k], deg)(x) for k in range(len(kn) - deg - 1)])[3:-3]
    t = np.arange(dt / 2, T, dt)
    F = (B * wx) @ np.exp(1j * np.outer(x, t)); W = (t ** 2 + 0.25) ** 2
    N = 2 * np.real((F * (W * dt)) @ F.conj().T); Q = 2 * np.real((F * (W * K.symbol(t, L) * dt)) @ F.conj().T)
    return float(eigh(Q, N, eigvals_only=True)[0])


def lp(L, span, hb, db):
    xi = np.arange(0, XI_MAX, DXI); wt = (xi ** 2 + 0.25) ** 2; uk = np.arange(L + W_HAT, L + span, W_HAT)
    while Fraction(float(uk.min())) - Fraction(W_HAT) < Fraction(L):   # exact: hat supports outside (-L, L)
        uk = np.nextafter(uk, np.inf)
    h = K.columns(xi, L, W_HAT, uk); c = np.zeros(h.shape[1] + 1); c[-1] = -1
    r = linprog(c, A_ub=np.hstack([-h, wt[:, None]]), b_ub=wt * K.symbol(xi, L),
                bounds=[(-hb, hb)] * (h.shape[1] - 5) + [(-db, db)] * 5 + [(None, None)], method="highs")
    if r.status != 0 or r.x is None:
        return None
    return {"L": L, "w": W_HAT, "span": span, "uk": uk.tolist(), "coef": r.x[:-1].tolist(), "m": float(r.x[-1]),
            "bound": hb, "delta_bound": db}


def fine_min(P):
    L = P["L"]; c = np.array(P["coef"]); uk = np.array(P["uk"]); best = (math.inf, None)
    f = np.arange(0, XI_MAX, FINE)
    for s in range(0, len(f), 300000):
        x = f[s:s + 300000]; W = (x ** 2 + 0.25) ** 2
        G = (W * K.symbol(x, L) + K.columns(x, L, P["w"], uk) @ c) / W; i = int(np.argmin(G))
        if G[i] < best[0]: best = (float(G[i]), float(x[i]))
    return best


def arb(lp_path, m, z0, out):
    p = subprocess.run([sys.executable, os.path.join(HERE, "krein_arb_receipt_v2.py"), "run", lp_path,
                        repr(m), "3000", repr(z0), out], capture_output=True, text=True)
    rec = json.load(open(out)) if os.path.exists(out) else {}
    stdout = open(out + ".stdout").read() if os.path.exists(out + ".stdout") else p.stdout + p.stderr
    return rec, stdout


def calibrate(L, outdir):
    os.makedirs(outdir, exist_ok=True); log = {"L": L, "rungs": [], "attempts": []}
    mstar = primal_margin(L); log["primal_margin"] = mstar
    save = lambda: json.dump(log, open(os.path.join(outdir, f"calibration_L{L}.json"), "w"), indent=1)
    if mstar <= 0:
        log["verdict"] = "NO_CERTIFICATE_POSSIBLE (primal margin <= 0)"; save(); return 1
    for span, hb, db in LADDER:
        P = lp(L, span, hb, db); rung = {"span": span, "hat_bound": hb, "delta_bound": db,
                                         "lp_m": None if P is None else P["m"]}
        log["rungs"].append(rung); save()
        if P is None or P["m"] <= 0:
            continue
        gmin, at = fine_min(P); rung["fine_min"] = gmin; rung["fine_min_at"] = at
        if gmin <= 0:
            continue
        lp_path = os.path.join(outdir, f"krein_lp_L{L}.json"); json.dump(P, open(lp_path, "w"))
        m, z0 = FRACTION * gmin, 0.02
        for k in range(MAX_TRIES):
            out = os.path.join(outdir, f"KREIN_ARB_RECEIPT_L{L}.json")
            rec, stdout = arb(lp_path, m, z0, out)
            log["attempts"].append({"m": m, "zero_cell": z0, "status": rec.get("status"),
                                    "cells": rec.get("result", {}).get("cells_verified")}); save()
            if rec.get("status") == "EXECUTION_BOUND":
                log["verdict"] = "CERTIFIED"; save(); return 0
            if "assert lbz > 0" in stdout:
                z0 /= 2
            else:
                m *= BACKOFF
        log["verdict"] = "ARB_FAILED_AFTER_RETRIES"; save(); return 1
    log["verdict"] = "NO_POSITIVE_LP_ON_LADDER"; save(); return 1


def table(outdir):
    rows = ["| L | primal m* | m_cert | cells (verifier) | zero-cell lb | tail F/W | receipt |", "|---|---|---|---|---|---|---|"]
    for fn in sorted(os.listdir(outdir)):
        if fn.startswith("KREIN_ARB_RECEIPT_L") and fn.endswith(".json"):
            r = json.load(open(os.path.join(outdir, fn))); L = r["parameters"]["L"]
            cal = json.load(open(os.path.join(outdir, f"calibration_L{L}.json")))
            rows.append(f"| {L} | {cal['primal_margin']:.4g} | {r['parameters']['m']} | {r['result']['cells_verified']} | "
                        f"{float(r['result']['zero_cell_lower_bound']):.3g} | {float(r['result']['tail_lower_bound_F_over_W']):.3g} | "
                        f"{r['status']} `{r['receipt_sha256'][:12]}` |")
    print("\n".join(rows))


if __name__ == "__main__":
    if sys.argv[1] == "table":
        table(sys.argv[2])
    else:
        sys.exit(calibrate(float(sys.argv[1]), sys.argv[2]))
