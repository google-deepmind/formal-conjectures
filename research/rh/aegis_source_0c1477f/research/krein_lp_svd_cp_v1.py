"""Reduced-basis Krein dual LP with cutting plane (generator of krein_lp_L1.05.json).

The raw hat/delta LP is numerically singular at L >= 1 (HiGHS status 4): neighbouring hat
columns cos(xi u) sinc^2 / W are nearly collinear on xi in [0, 40]. Here the row-scaled column
matrix (constraint S - m + Hhat/W >= 0) is replaced by its leading left singular vectors
(singular values > rtol * s_max), the LP is solved over that orthonormal basis with |d4| <= 3
(tail check of verify_krein_arb_v1.py), violated local minima of a 0.0005 grid on [0, 300] are
added as rows, and every iterate with a positive fine-grid minimum is saved.
The floating fine-grid minimum is NOT a certificate; verify_krein_arb_v1.py is.

usage: python3 krein_lp_svd_cp_v1.py L SPAN W RTOL [OUTDIR]
krein_lp_L1.05.json = iterate 2 of `python3 krein_lp_svd_cp_v1.py 1.05 8 0.02 3e-10`.
RH_PROVEN=false; authority_effect=NONE."""
import sys, math, time, json
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog
from scipy.signal import argrelmin
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import krein_dual_beyond_log2 as K
OUT = sys.argv[5] if len(sys.argv) > 5 else "."
def rows(x, L, w, uk): return K.columns(x, L, w, uk) / ((x**2+0.25)**2)[:, None]
def run(L, span, w, rtol, B=1e3, D4=3.0, rounds=12):
    uk = np.arange(L+w, L+span, w)
    while Fraction(float(uk.min())) - Fraction(w) < Fraction(L): uk = np.nextafter(uk, np.inf)
    x0 = np.r_[np.arange(0, 150, 0.01), np.arange(150, 300, 0.05)]
    U, s, Vt = np.linalg.svd(rows(x0, L, w, uk), full_matrices=False)
    r = int((s > rtol*s[0]).sum()); T = Vt[:r].T / s[:r]          # c = T y
    X = x0.copy(); fine = np.arange(0, 300, 0.0005); best = None
    for it in range(rounds):
        R = rows(X, L, w, uk) @ T
        Aub = np.vstack([np.hstack([-R, np.ones((len(X), 1))]), np.r_[T[-1], 0], np.r_[-T[-1], 0]])
        res = linprog(np.r_[np.zeros(r), -1], A_ub=Aub, b_ub=np.r_[K.symbol(X, L), D4, D4],
                      bounds=[(-B, B)]*r + [(None, None)], method="highs")
        if res.x is None:
            return best if best else {"status": res.status, "it": it, "r": r}
        y, m = res.x[:-1], res.x[-1]; c = T @ y
        g = np.concatenate([K.symbol(f, L) + rows(f, L, w, uk) @ c for f in np.array_split(fine, 30)])
        gmin = float(g.min())
        if gmin > 0 and (best is None or gmin > best["fine_min"]):
            best = {"L": L, "w": w, "span": span, "uk": uk.tolist(), "coef": c.tolist(), "m_lp": float(m), "fine_min": gmin,
                    "rank": r, "rtol": rtol, "d": c[-5:].tolist(), "sum_abs": float(np.abs(c[:-5]).sum()), "it": it}
            json.dump(best, open(f"{OUT}/best_L{L}_s{span}_r{rtol:g}.json", "w"))
        print(f"  it={it} rows={len(X)} m_lp={m:.6g} fine_min={gmin:.6g} @ {fine[int(np.argmin(g))]:.3f}", flush=True)
        if gmin >= 0.97*m: break
        loc = argrelmin(g)[0]; new = fine[loc[g[loc] < m]]
        X = np.unique(np.r_[X, new])
    return best if best else {"status": "no positive candidate"}
if __name__ == "__main__":
    L, span, w, rtol = map(float, sys.argv[1:5])
    b = run(L, span, w, rtol)
    if "coef" not in b: print("FAILED", b); sys.exit(1)
    print(f"RESULT L={L} span={span} rtol={rtol:g} rank={b['rank']} m_lp={b['m_lp']:.6g} fine_min={b['fine_min']:.6g} d4={b['d'][-1]:.3g} sum|c|={b['sum_abs']:.3g}", flush=True)
    json.dump(b, open(f"{OUT}/svdcp_L{L}_s{span}_r{rtol:g}.json", "w"))
