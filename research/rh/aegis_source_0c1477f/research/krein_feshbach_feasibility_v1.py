"""Full-space Feshbach (Schur) feasibility for the restricted Weil form at fixed L.

Floating-point diagnostic (T1).  Nothing here is interval-certified.

Setting.  H = moment-zero subspace of L^2[0, L]; for G in H with Fourier
transform G^(xi) = int G(x) e^{i xi x} dx,

    Q(G) = (1/2pi) int |G^|^2 S,   ||G||^2 = (1/2pi) int |G^|^2,
    S(xi) = Re psi(1/4 + i xi/2) - log pi - sum_{log n < L} 2 Lambda(n) n^{-1/2} cos(xi log n),

so the operator is A = P_H M_S P_H.  Split H = P1 H (+) P2 H with P1 spanned by the
k lowest Ritz vectors of a B-spline moment-zero basis.  Then A >= mu on all of H if

    A11 - mu - C_B / (c_inf - mu) > 0,   c_inf <= inf_{P2 H} A,   C_B >= B B^*.

Ingredients (each in the direction a rigorous version needs):
  * A11: exact compression on P1 (Fourier quadrature to XI_MAX).
  * C_B = <P_L M_S phi_i, P_L M_S phi_j> - A11^2 >= B B^*   (P_H <= P_L).
  * c_inf: a genuine Krein certificate W(S - c) + H^ + W s >= 0 pointwise, with H built
    from hats and order-19 edge splines supported in |u| >= L (pairs to zero against
    |G1^|^2, RHKreinGenuineCertificateV1 / RHKreinSplineDerivativesV1), slack s >= 0
    allowed only on |xi| <= XI0.  Then A - c >= -P_L M_s P_L on H, so
    c_inf >= c - ||P2 T_s P2|| (exact top eigenvalue and Hilbert-Schmidt bound reported).

Usage: python3 krein_feshbach_feasibility_v1.py L k c_target XI0 [OUT.json]
"""
import json
import math
import sys

import numpy as np
from scipy.interpolate import BSpline
from scipy.linalg import eigh
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack
from scipy.special import digamma

L, K = float(sys.argv[1]), int(sys.argv[2])
C_TARGET, XI0 = float(sys.argv[3]), float(sys.argv[4])
OUT = sys.argv[5] if len(sys.argv) > 5 else None
NB, DEG, NGL = 60, 7, 24
DXI, XI_MAX = 0.01, 3000.0
MUS = (0.00025, 0.001, 0.0015, 0.002, 0.0025)


def von_mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0


PRIME_POWERS = [(math.log(n), von_mangoldt(n) / math.sqrt(n))
                for n in range(2, int(math.exp(L)) + 1)
                if math.log(n) < L and von_mangoldt(n) > 0]


def symbol(xi):
    s = np.real(digamma(0.25 + 0.5j * xi)) - math.log(math.pi)
    for log_n, weight in PRIME_POWERS:
        s = s - 2 * weight * np.cos(xi * log_n)
    return s


# moment-zero basis G = (1/4 - D^2) b, b a degree-7 B-spline with 3 end splines dropped
knots = np.concatenate([[0] * DEG, np.linspace(0, L, NB - DEG + 1), [L] * DEG])
breaks = np.linspace(0, L, NB - DEG + 1)
u, w = np.polynomial.legendre.leggauss(NGL)
x = np.concatenate([(a + b) / 2 + (b - a) / 2 * u for a, b in zip(breaks[:-1], breaks[1:])])
wx = np.concatenate([(b - a) / 2 * w for a, b in zip(breaks[:-1], breaks[1:])])
sw = np.sqrt(wx)
nbas = len(knots) - DEG - 1
basis = []
for j in range(3, nbas - 3):
    spline = BSpline(knots, np.eye(nbas)[j], DEG)
    basis.append(-spline.derivative(2)(x) + 0.25 * spline(x))
q, _ = np.linalg.qr((np.array(basis) * sw).T)
phi = q.T / sw                                   # L^2[0,L]-orthonormal rows on nodes

xi_grid = np.arange(DXI / 2, XI_MAX, DXI)
s_grid = symbol(xi_grid)


def fourier(rows, xs):
    return (rows * wx) @ np.exp(1j * np.outer(x, xs))


def compress(rows):
    """Return (rows A rows^T, P_L M_S rows on nodes)."""
    a = np.zeros((rows.shape[0],) * 2)
    v = np.zeros((rows.shape[0], len(x)))
    for lo in range(0, len(xi_grid), 20000):
        xs = xi_grid[lo:lo + 20000]
        f = fourier(rows, xs) * (s_grid[lo:lo + 20000] * DXI / np.pi)
        a += np.real(f @ fourier(rows, xs).conj().T)
        v += np.real(f @ np.exp(-1j * np.outer(xs, x)))
    return a, v


a_full, _ = compress(phi)
ritz, vecs = eigh(a_full)
p1 = vecs[:, :K].T @ phi
a11, v1 = compress(p1)
c_b = (v1 * wx) @ v1.T - a11 @ a11


def column(xs, centre, width, order):
    return 2 * np.cos(xs * centre) * np.sinc(xs * width / (2 * math.pi)) ** order * width


specs = [(c, 0.02, 2) for c in np.arange(L + 0.02, L + 4.0, 0.02)]
specs += [(L + 19 * 0.002 / 2 + j * 0.002, 0.002, 19) for j in range(40)]
xg = np.arange(0, 300, 0.01)
wg = (xg ** 2 + 0.25) ** 2
hb = np.array([column(xg, *s) for s in specs]).T
ns = int((xg <= XI0).sum())
slack_block = csr_matrix((-wg[:ns], (np.arange(ns), np.arange(ns))), shape=(len(xg), ns))
lp = linprog(np.concatenate([np.zeros(len(specs)), np.full(ns, 0.01)]),
             A_ub=hstack([csr_matrix(-hb), slack_block]).tocsr(),
             b_ub=wg * (symbol(xg) - C_TARGET),
             bounds=[(-1e6, 1e6)] * len(specs) + [(0, None)] * ns, method='highs')
if lp.status != 0:
    raise SystemExit(f'LP failed: status {lp.status}')
coef, slack = lp.x[:len(specs)], lp.x[len(specs):]

fine_min = np.inf
for lo in range(0, 3000, 100):
    z = np.arange(lo, lo + 100, 0.0005)
    wz = (z ** 2 + 0.25) ** 2
    f = (wz * (symbol(z) - C_TARGET) + np.array([column(z, *s) for s in specs]).T @ coef) / wz
    fine_min = min(fine_min, float((f + np.interp(z, xg[:ns], slack, right=0.0)).min()))
c_eff = C_TARGET + min(0.0, fine_min)            # absorb fine-grid deficit into the target

d = slack * 0.01 / np.pi
cos_x, sin_x = np.cos(np.outer(x, xg[:ns])), np.sin(np.outer(x, xg[:ns]))
t_s = sw[:, None] * ((cos_x * d) @ cos_x.T + (sin_x * d) @ sin_x.T) * sw[None, :]
u1 = (p1 * sw).T
proj = np.eye(len(x)) - u1 @ u1.T
tail_eigs = np.linalg.eigvalsh(proj @ t_s @ proj)
tail_top = float(tail_eigs.max())
tail_hs = float(np.sqrt(np.sum(tail_eigs ** 2)))

result = {
    'schema': 'AEGIS_KREIN_FESHBACH_FEASIBILITY_V1',
    'status': 'FLOATING_POINT_DIAGNOSTIC_NOT_A_CERTIFICATE',
    'L': L, 'k': K, 'basis_dim': int(phi.shape[0]),
    'ritz_lambda_min': float(ritz[0]), 'ritz_lambda_k_plus_1': float(ritz[K]),
    'c_target': C_TARGET, 'xi0_slack_support': XI0,
    'lp_slack_integral': float(lp.fun), 'fine_grid_min_F_plus_s': fine_min,
    'tail_top_eig': tail_top, 'tail_hs_bound': tail_hs,
    'c_inf_top': c_eff - tail_top, 'c_inf_hs': c_eff - tail_hs,
    'c_b_on_lowest_ritz': float(c_b[0, 0]),
    'schur_margin_hs': {},
}
for mu in MUS:
    m = a11 - mu * np.eye(K) - c_b / (result['c_inf_hs'] - mu)
    result['schur_margin_hs'][str(mu)] = float(np.linalg.eigvalsh(m).min())
print(json.dumps(result, indent=1))
if OUT:
    json.dump(result, open(OUT, 'w'), indent=1, sort_keys=True)
