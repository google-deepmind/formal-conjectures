"""Weil positivity past log 2: primal eigenvalue vs. Fourier-side (Krein) dual certificate.

Numerics only (T2).  Not RH.  AUTHORITY_EFFECT = NONE.

Moment-zero g on [0, L] factors as g = (1/4 - D^2) g1 with g1, g1' vanishing at 0 and L,
so ghat(xi) = (xi^2 + 1/4) g1hat(xi) and, for support length L < log 3 (only n = 2 enters),

    Q(g) = (1/2pi) int |g1hat|^2 W(xi) S(xi) dxi,   W = (xi^2 + 1/4)^2,
    S(xi) = Re psi(1/4 + i xi/2) - log pi - sqrt(2) log 2 cos(xi log 2)   (last term only if L > log 2).

Dual certificate: an even distribution H supported in |u| >= L (hats on [L, L + span] plus
delta^(j) at +-L for j <= 4, which pair to zero with g1 * g1~ since it vanishes to order 5 at +-L)
with W (S - m) + Hhat >= 0 on the real line gives Q(g) >= m E for every such g.

Usage: python3 krein_dual_beyond_log2.py 0.6931 0.72 0.8
"""
import math
import sys

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
from scipy.optimize import linprog
from scipy.special import digamma

LOG2 = math.log(2)


def symbol(xi, L):
    assert L < math.log(3)
    s = np.real(digamma(0.25 + 0.5j * xi)) - math.log(math.pi)
    if L > LOG2:
        s = s - math.sqrt(2) * LOG2 * np.cos(xi * LOG2)
    return s


def primal(L, n=24, T=3000.0, dt=0.01):
    """Smallest Q(g)/E over g = (1/4 - D^2)(sin(pi x/L) sin(k pi x/L)), k = 1..n."""
    xs, ws = leggauss(1200)
    x, ww = (xs + 1) * L / 2, ws * L / 2
    k, a = np.arange(1, n + 1)[:, None], math.pi / L
    s1, c1, sk, ck = np.sin(a * x), np.cos(a * x), np.sin(k * a * x), np.cos(k * a * x)
    g = 0.25 * s1 * sk - (-a * a * s1 * sk + 2 * a * a * k * c1 * ck - (k * a) ** 2 * s1 * sk)
    t = np.arange(0, T, dt) + dt / 2
    f = (g * ww) @ np.exp(-1j * np.outer(x, t))
    q = 2 * ((f * symbol(t, L)) @ f.conj().T).real * dt / (2 * math.pi)
    return eigh(q, (g * ww) @ g.T, eigvals_only=True)[0]


def columns(xi, L, w, uk):
    hats = 2 * np.cos(np.outer(xi, uk)) * (np.sinc(xi * w / (2 * math.pi)) ** 2 * w)[:, None]
    bd = np.array([xi**j * (np.cos(xi * L) if j % 2 == 0 else np.sin(xi * L)) for j in range(5)]).T
    return np.hstack([hats, bd])


def dual(L, w=0.02, span=4.0, xi_max=300.0, dxi=0.01, bound=1e5):
    xi = np.arange(0, xi_max, dxi)
    wt = (xi**2 + 0.25) ** 2
    uk = np.arange(L + w, L + span, w)
    h = columns(xi, L, w, uk)
    a_ub = np.hstack([-h, wt[:, None]])
    c = np.zeros(h.shape[1] + 1)
    c[-1] = -1
    r = linprog(c, A_ub=a_ub, b_ub=wt * symbol(xi, L),
                bounds=[(-bound, bound)] * h.shape[1] + [(None, None)], method="highs")
    m, coef = r.x[-1], r.x[:-1]
    worst = np.inf  # re-check between LP nodes on a 20x finer grid up to 3000
    for lo in range(0, 3000, 50):
        z = np.arange(lo, lo + 50, dxi / 20)
        wz = (z**2 + 0.25) ** 2
        worst = min(worst, ((wz * (symbol(z, L) - m) + columns(z, L, w, uk) @ coef) / wz).min())
    # xi >= 3000: Re psi increases in |xi|, |cos| <= 1, xi^4 / W <= 1 and xi^j / W decreases for j < 4
    z = 3000.0
    om = np.real(digamma(0.25 + 0.5j * z)) - math.log(math.pi) - (math.sqrt(2) * LOG2 if L > LOG2 else 0.0)
    tail = abs(coef[-1]) + sum(abs(coef[-5 + j]) * z**j for j in range(4)) / z**4 \
        + 2 * np.abs(coef[:-5]).sum() * w / z**4
    return m, worst, om - m - tail


if __name__ == "__main__":
    for L in [float(v) for v in sys.argv[1:]] or [0.6931, 0.72, 0.8]:
        m, worst, tail = dual(L)
        print(f"L={L:.4f} primal={primal(L):.4f} dual m={m:.4f} fine-grid slack={worst:.2e} tail slack={tail:.3f}")
