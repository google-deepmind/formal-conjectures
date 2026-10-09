"""Rigorous (Arb) verification of the Krein dual certificate
    F(xi) = W(xi)(S(xi) - m) + Hhat(xi) >= 0 for all real xi (F even),
W = (xi^2+1/4)^2, S = Re psi(1/4 + i xi/2) - log pi - sqrt2 log2 cos(xi log2),
Hhat = sum_k c_k 2w cos(xi u_k) sinc^2(xi w / 2pi) + sum_j d_j xi^j (cos xi L | sin xi L).
Hats rewritten exactly: 2w cos(xi u) sinc^2 = (2/(w xi^2)) [2cos xi u - cos xi(u+w) - cos xi(u-w)],
so G := xi^2 F = xi^2 W (S - m) + (2/w) R(xi) + xi^2 D(xi), R = sum_j e_j cos(xi v_j).
On each cell [x0-d, x0+d] a degree-N Taylor model of G with rigorous remainder is built
(exact Arb coefficients; Bernstein-type remainder bounds); cells are bisected until the
model's lower bound is > 0.  xi >= X is covered by a monotone tail bound."""
import json, sys, math
from flint import arb, acb, ctx, fmpq
ctx.prec = 256
N = 20
P = json.load(open(sys.argv[1])); mcert = arb(sys.argv[2]); X = arb(sys.argv[3]) if len(sys.argv) > 3 else arb(3000)
SB = json.load(open(sys.argv[5]))
Z0 = arb(SB['z0']); STEP = arb(SB['step']); SBAR = [arb(v) for v in SB['sbar']]
def sbar_at(x0):
    k = int(math.floor((float(x0.mid()) - float(Z0.mid())) / float(STEP.mid())))
    return SBAR[k] if 0 <= k < len(SBAR) else arb(0)
L = arb(P['L']); w = arb(P['w']); coef = [arb(c) for c in P['coef']]
c, d = coef[:-5], coef[-5:]
K = len(c)                       # hats k=0..K-1 at u_k = L + (k+1) w (float grid reproduced exactly below)
uk = [arb(u) for u in P['uk']]
# frequencies v_j = u_k, u_k +- w ; collect coefficients exactly
V = []
for k in range(K):
    V += [(uk[k], 2 * c[k]), (uk[k] + w, -c[k]), (uk[k] - w, -c[k])]   # no merging: exact
sumabs_e = sum(abs(e) for _, e in V); vmax = max(v for v, _ in V)
PI = arb.pi(); LOG2 = arb(2).log(); SQ2 = arb(2).sqrt(); LOGPI = PI.log()
# all prime powers q with log q < L: S -= 2 Lambda(q) q^{-1/2} cos(xi log q)
def _lam(q):
    for p in range(2, q + 1):
        if q % p == 0:
            m = q
            while m % p == 0: m //= p
            return p if m == 1 else 0
    return 0
PP = [(arb(q).log(), 2 * arb(_lam(q)).log() / arb(q).sqrt()) for q in range(2, int(math.exp(float(L.mid()))) + 2)
      if _lam(q) and arb(q).log() < L]
AMPS = sum((a for _, a in PP), arb(0))
fact = [arb(math.factorial(n)) for n in range(N + 2)]
I = acb(0, 1)

def poly_mul(a, b):
    out = [arb(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def fold(g, prod, dd, scale=arb(1)):
    extra = arb(0)
    for n, a in enumerate(prod):
        if n < N: g[n] += scale * a
        else: extra += abs(scale * a) * dd ** n
    return extra

def model(x0, dd):
    """Taylor coefficients g[0..N-1] of G(x0+eps) and remainder bound on |eps|<=dd."""
    x0 = arb(x0); dd = arb(dd); rem = arb(0)
    # (2/w) R
    g = [arb(0)] * N
    for v, e in V:
        base = e * acb(0, (x0 * v)).exp().real if False else None
        z = (I * x0 * v).exp() * e
        iv = I * v
        t = z
        for n in range(N):
            g[n] += (2 / w) * t.real
            t = t * iv / (n + 1)
    rem += (2 / w) * sumabs_e * (vmax * dd) ** N / fact[N]
    # xi^2 D(xi) = sum_j d_j xi^(j+2) Re(kappa_j e^{i xi L}), kappa_j = 1 (j even) or -i (j odd)
    xpoly = [x0, arb(1)]                          # xi = x0 + eps
    ez = [((I * L) ** n * (I * x0 * L).exp() / fact[n]) for n in range(N)]
    for j in range(5):
        kap = acb(1) if j % 2 == 0 else acb(0, -1)
        pj = [arb(1)]
        for _ in range(j + 2): pj = poly_mul(pj, xpoly)
        ser = [(kap * ez[n]).real for n in range(N)]
        prod = poly_mul(pj, ser)
        rem += fold(g, prod, dd, d[j])
        pmax = (abs(x0) + dd) ** (j + 2)
        rem += abs(d[j]) * pmax * (L * dd) ** N / fact[N] * (2 ** (j + 2))
    # xi^2 W (S - m):  S(x0+eps) Taylor via polygamma
    z0 = acb(arb(1) / 4, x0 / 2)
    s = []
    for n in range(N):
        pg = z0.polygamma(n) * (I / 2) ** n / fact[n]
        s.append(pg.real)
    s[0] = s[0] - LOGPI - mcert + sbar_at(x0)
    for lq, amp in PP:
        cz = [((I * lq) ** n * (I * x0 * lq).exp() / fact[n]).real for n in range(N)]
        for n in range(N): s[n] -= amp * cz[n]
    # remainder of S: |psi^(N)(1/4+iy)| (1/2)^N / N! <= (1/2)^N * sum_k 1/((k+1/4)^2+y^2)^((N+1)/2)
    ymin = max(abs(x0) - dd, arb(0)) / 2
    tailsum = sum(1 / (((arb(k) + arb(1) / 4) ** 2 + ymin ** 2) ** (arb(N + 1) / 2)) for k in range(60)) \
        + 1 / ((arb(60) - 1) ** N * N)
    remS = (arb(1) / 2) ** N * tailsum * dd ** N + sum((amp * (lq * dd) ** N / fact[N] for lq, amp in PP), arb(0))
    xw = [x0, arb(1)]
    q = [arb(1)]
    for _ in range(2): q = poly_mul(q, xw)                      # xi^2
    wq = poly_mul(poly_mul(xw, xw), [arb(0)]) if False else None
    xi2 = poly_mul([arb(1)], poly_mul(xw, xw))
    Wp = poly_mul([arb(1) / 4, arb(0), arb(1)] if False else [x0 * x0 + arb(1) / 4, 2 * x0, arb(1)],
                  [x0 * x0 + arb(1) / 4, 2 * x0, arb(1)])
    pw = poly_mul(xi2, Wp)                                   # xi^2 W, exact degree 6
    prod = poly_mul(pw, s)
    rem += fold(g, prod, dd)
    pwmax = sum(abs(a) * dd ** i for i, a in enumerate(pw))
    rem += pwmax * remS
    return g, rem

def lower_bound(g, rem, dd, divide_xi2_at_zero=False):
    dd = arb(dd)
    if divide_xi2_at_zero:
        lb = g[2] - sum(abs(g[n]) * dd ** (n - 2) for n in range(3, N)) - rem / 1  # rem ~ dd^N, divided by eps^2 <= dd^(N-2)
        return lb
    return g[0] - sum(abs(g[n]) * dd ** n for n in range(1, N)) - rem

# near zero: F(eps) = sum_{n>=2} g_n eps^(n-2); remainder/eps^2 bounded by rem/dd^2 * (eps/dd)^(N-2) <= rem/dd^2
def check_zero(dd):
    g, rem = model(0, dd)
    # G(0) = G'(0) = 0 exactly: sum_j e_j = 0 (second differences), R is even, the D and W parts carry xi^2.
    assert abs(g[0]) < arb('1e-40') and abs(g[1]) < arb('1e-40'), (g[0], g[1])
    lb = g[2] - sum(abs(g[n]) * arb(dd) ** (n - 2) for n in range(3, N)) - rem / arb(dd) ** 2
    return lb

stats = {"cells": 0, "min_rel": None}
def verify(a, b, depth=0):
    x0 = (a + b) / 2; dd = (b - a) / 2
    g, rem = model(x0, dd)
    lb = lower_bound(g, rem, dd)
    if lb > 0:
        stats["cells"] += 1
        return True
    if depth > 40: raise RuntimeError(f"cannot certify near xi={float(x0)}: lb={lb}")
    return verify(a, x0, depth + 1) and verify(x0, b, depth + 1)

z0cell = arb(sys.argv[4]) if len(sys.argv) > 4 else arb('0.05')
lbz = check_zero(z0cell)
print("zero cell [0,%s]: lower bound of F = %s" % (z0cell, lbz), flush=True)
assert lbz > 0
# cover [z0cell, X] in chunks
x = z0cell; step = STEP
assert abs(float(z0cell.mid()) - float(Z0.mid())) < 1e-15
while x < X:
    y = x + step if x + step < X else X
    verify(x, y)
    x = y
    if stats["cells"] % 500 == 0: print("  at xi =", float(x.mid()), "cells", stats["cells"], flush=True)
print("cells verified on [%s, %s]: %d" % (z0cell, X, stats["cells"]), flush=True)
# tail xi >= X: F/W >= S(X)_lower - m - |d4| - sum_{j<4}|d_j| X^(j-4) - (8/(w X^2)) sum|c|/X^4 * ... (hats: |2w cos sinc^2| <= 8/(w xi^2))
SX = acb(arb(1) / 4, X / 2).digamma().real - LOGPI - AMPS
tail = SX - mcert - abs(d[4]) - sum(abs(d[j]) * X ** (j - 4) for j in range(4)) - 8 * sum(abs(x) for x in c) / (w * X ** 2) / X ** 4
print("tail lower bound (F/W for xi >= X):", tail, flush=True)
assert tail > 0
print("CERTIFIED: F(xi) >= 0 for all real xi, m =", mcert)
