"""Exact (Fraction) mirror of the Lean L = 21/20 checker (RHKreinL105CheckerV1).

Every function here has a Lean twin of the same name; integer/rational semantics are identical
(floor/ceil rounding to 2^-P, no floats).  Used to choose wide cells and breakpoints and to
predict `checkWide ... = true` before the kernel runs.
"""
from fractions import Fraction as Q
from math import factorial, floor, ceil
import json
from pathlib import Path

def fl(q): return q.numerator // q.denominator
def cl(q): return -((-q.numerator) // q.denominator)
def roundQ(k, q): return Q(fl(q * 2**k), 2**k)
def roundUpQ(k, q): return Q(cl(q * 2**k), 2**k)

# ---- polynomials (lists, constant first) ----
def padd(p, q):
    if len(p) < len(q): p, q = q, p
    return [a + (q[i] if i < len(q) else 0) for i, a in enumerate(p)]
def psmul(c, p): return [c * a for a in p]
def pmul(p, q):
    if not p or not q: return []
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0: continue
        for j, b in enumerate(q): out[i + j] += a * b
    return out
def absBound(p, r):
    acc = Q(0)
    for a in reversed(p): acc = abs(a) + r * acc
    return acc
def floorBound(p, r):
    if not p: return Q(0)
    return p[0] - r * absBound(p[1:], r)
def evalQ(p, x):
    acc = Q(0)
    for a in reversed(p): acc = a + x * acc
    return acc

# ---- Taylor models (p, e) ----
def tm_add(T, U): return (padd(T[0], U[0]), T[1] + U[1])
def tm_neg(T): return (psmul(-1, T[0]), T[1])
def tm_sub(T, U): return tm_add(T, tm_neg(U))
def tm_smul(c, T): return (psmul(c, T[0]), abs(c) * T[1])
def tm_mul(r, T, U): return (pmul(T[0], U[0]), T[1] * absBound(U[0], r) + absBound(T[0], r) * U[1] + T[1] * U[1])
def tm_const(a): return ([a], Q(0))
def tm_ball(a, e): return ([a], e)
def tm_trim(k, n, r, T):
    q = [roundQ(k, a) for a in T[0][:n]]
    return (q, roundUpQ(k, T[1] + absBound(padd(T[0], psmul(-1, q)), r)))

# ---- trig (as in RHKreinTrigTMV1 / RHKreinRotTMV1) ----
def cosCoef(m): return Q((-1) ** (m // 2), factorial(m)) if m % 2 == 0 else Q(0)
def sinCoef(m): return Q((-1) ** (m // 2), factorial(m)) if m % 2 == 1 else Q(0)
def coefFrom(f, h, k, n):  # [f(k) h^k, f(k+1) h^(k+1), ...] length n
    return [f(k + i) * h ** (k + i) for i in range(n)]
def taylorErr(n, x): return x ** n * Q(n + 1, factorial(n) * n)
def cosScaledTM(n, r, h):
    if 0 < n and 0 <= r and r * abs(h) <= 1: return (coefFrom(cosCoef, h, 0, n), taylorErr(n, r * abs(h)))
    return ([], Q(1))
def sinScaledTM(n, r, h):
    if 0 < n and 0 <= r and r * abs(h) <= 1: return (coefFrom(sinCoef, h, 0, n), taylorErr(n, r * abs(h)))
    return ([], Q(1))
def dbl(P, A):
    c, s, e = A
    return (roundQ(P, c * c - s * s), roundQ(P, 2 * c * s), roundUpQ(P, 2 * e * (2 + e) + Q(1, 2**P)))
def dblN(P, k, A):
    for _ in range(k): A = dbl(P, A)
    return A
def baseCS(n, P, x):
    c = evalQ(coefFrom(cosCoef, Q(1), 0, n), x); s = evalQ(coefFrom(sinCoef, Q(1), 0, n), x)
    return (roundQ(P, c), roundQ(P, s), roundUpQ(P, taylorErr(n, abs(x)) + Q(1, 2**P)))
def cosSin(n, k, P, a):
    if 0 < n and abs(a / 2**k) <= 1: return dblN(P, k, baseCS(n, P, a / 2**k))
    return (Q(0), Q(0), Q(1))
def cosAffTM(q, r, c, h):
    n, nb, k, P = q; A = cosSin(nb, k, P, c * h)
    return tm_sub(tm_mul(r, tm_ball(A[0], A[2]), cosScaledTM(n, r, h)), tm_mul(r, tm_ball(A[1], A[2]), sinScaledTM(n, r, h)))
def sinAffTM(q, r, c, h):
    n, nb, k, P = q; A = cosSin(nb, k, P, c * h)
    return tm_add(tm_mul(r, tm_ball(A[1], A[2]), cosScaledTM(n, r, h)), tm_mul(r, tm_ball(A[0], A[2]), sinScaledTM(n, r, h)))
def invCoef(c, k): return Q((-1) ** k) / c ** (k + 1)
def invTM(K, r, c): return ([invCoef(c, k) for k in range(K)], r ** K / (c ** K * (c - r)))
def sincAffTM(q, K, r, c, d):
    if 0 <= r and r < c and 0 < d: return tm_mul(r, sinAffTM(q, r, c, 1 / d), tm_smul(d, invTM(K, r, c)))
    return ([], Q(1))
def tmPow(r, P, D, T, m):
    acc = tm_const(Q(1))
    for _ in range(m): acc = tm_trim(P, D, r, tm_mul(r, acc, T))
    return acc
def rotC(P, A, B):
    return (roundQ(P, A[0] * B[0] - A[1] * B[1]), roundQ(P, A[0] * B[1] + A[1] * B[0]),
            roundUpQ(P, A[2] + (1 + A[2]) * B[2] + Q(2, 2**P)))
def baseZ(n, P, x):
    return (roundQ(P, evalQ(coefFrom(cosCoef, Q(1), 0, n), x)), roundQ(P, evalQ(coefFrom(sinCoef, Q(1), 0, n), x)),
            roundUpQ(P, taylorErr(n, abs(x)) + Q(2, 2**P)))
def dblZ(P, k, A):
    for _ in range(k): A = rotC(P, A, A)
    return A
def phaseZ(n, k, P, a):
    if 0 < n and abs(a / 2**k) <= 1: return dblZ(P, k, baseZ(n, P, a / 2**k))
    return (Q(0), Q(0), Q(1))
def sigma(m, C, S):
    return (-1) ** (m // 2) * C if m % 2 == 0 else -((-1) ** (m // 2) * S)
def phaseRow(C, S, h, n):
    out = []; t = Q(1)
    for k in range(n):
        out.append(sigma(k, C, S) * t); t = t * h / (k + 1)
    return out

# ---- certificate data ----
L105 = Q(21, 20)
def hk(k): return Q(107 + 2 * k, 100)          # u_k = 21/20 + (k+1)/50
_P = json.loads((Path(__file__).resolve().parents[2] / 'aegis_source_4d7578e' / 'research' / 'krein_lp_L1.05_svd.json').read_text())
CQ = [Q(x) for x in _P['coef'][:-5]]           # exact dyadic values of the float coefficients
DQ = [Q(x) for x in _P['coef'][-5:]]
NH = len(CQ)
SUMC = sum(abs(x) for x in CQ)

# column error: 2 (r h)^n / n!  (Complex.exp_bound', needs r h <= (n+1)/2)
def colErr2(n, r, h, A): return A[2] + (1 + A[2]) * 2 * (r * abs(h)) ** n / factorial(n)

def hatAcc(pa, r, c):
    n, nb, k, P, D, K = pa
    A = phaseZ(nb, k, P, c * hk(0)); B = phaseZ(nb, k, P, c / 50)
    p = []; e = Q(0)
    for j in range(NH):
        h = hk(j)
        if 0 < n and r * abs(h) <= Q(n + 1, 2):
            p = padd(p, psmul(CQ[j], phaseRow(A[0], A[1], h, n))); e += abs(CQ[j]) * colErr2(n, r, h, A)
        else:
            e += abs(CQ[j])
        A = rotC(P, A, B)
    return (p, e)

def hatTM(pa, r, c): return tm_trim(pa[3], pa[4], r, hatAcc(pa, r, c))

# crude hat bound for c - r > 0:  |(2/50) sinc(t/100)^2 sum c cos| <= (2/50) (100/(c-r))^2 SUMC
def hatBallTM(r, c):
    if 0 < c - r: return tm_ball(Q(0), Q(2, 50) * (100 / (c - r)) ** 2 * SUMC)
    return tm_ball(Q(0), Q(2, 50) * SUMC)

def tVar(c): return ([c, Q(1)], Q(0))

def deltaTM(pa, r, c):
    q = pa[:4]; P, D = pa[3], pa[4]
    C = cosAffTM(q, r, c, L105); S = sinAffTM(q, r, c, L105)
    T = tVar(c); T2 = tm_mul(r, T, T); T3 = tm_mul(r, T2, T); T4 = tm_mul(r, T2, T2)
    acc = tm_add(tm_add(tm_add(tm_add(tm_smul(DQ[0], C), tm_smul(DQ[1], tm_mul(r, T, S))),
                                tm_smul(DQ[2], tm_mul(r, T2, C))), tm_smul(DQ[3], tm_mul(r, T3, S))),
                 tm_smul(DQ[4], tm_mul(r, T4, C)))
    return tm_trim(P, D, r, acc)

def weightPoly(c):
    b = [c * c + Q(1, 4), 2 * c, Q(1)]
    return pmul(b, b)

# psi head: sum_{n<K0} [1/(n+1) - Re 1/(z0 + i s/2)],  z0 = (n+1/4) + i c/2
def headTM(K0, D, r, c):
    p = [Q(0)] * D; e = Q(0)
    for n in range(K0):
        a = Q(4 * n + 1, 4); m2 = a * a + c * c / 4
        zeta = max(a, abs(c) / 2)
        if not (r / 2 < zeta): return ([], Q(10) ** 9)
        br, bi = a / m2, -(c / 2) / m2                  # 1/z0
        rr, ri = -(c / 2) / (2 * m2), -a / (2 * m2)      # (-i/2)/z0 = (-i/2) conj(z0)/m2
        coeffs = []
        for m in range(D):
            coeffs.append(br)
            br, bi = br * rr - bi * ri, br * ri + bi * rr
        p = padd(p, psmul(-1, coeffs)); p[0] += Q(1, n + 1)
        e += (r / 2) ** D / (zeta ** D * (zeta - r / 2))
    return (p, e)

A0 = Q(1414213562, 1000000000) * Q(6931471806, 10000000000)
L0 = Q(287209, 414355)
GAMMA_U = Q(5773, 10000)
LOGPI_U = Q(1144729886, 1000000000)

def symTM(pa, K0, r, c):
    """head + (-gamma_u - logpi_u - 2/10^9) - A0 cos(t L0) - A0 t / 10^10."""
    q = pa[:4]
    H = headTM(K0, pa[4], r, c)
    return tm_sub(tm_sub(tm_add(H, tm_const(-GAMMA_U - LOGPI_U - Q(2, 10**9))), tm_smul(A0, cosAffTM(q, r, c, L0))),
                  tm_smul(A0 / 10**10, tVar(c)))

def wideTM(pa, K0, hats, r, c):
    q = pa[:4]; P, D, K = pa[3], pa[4], pa[5]
    Wt = (weightPoly(c), Q(0))
    if hats:
        S1 = sincAffTM(q, K, r, c, Q(100))
        H = tm_smul(Q(2, 50), tm_mul(r, tmPow(r, P, D, S1, 2), hatTM(pa, r, c)))
    else:
        H = hatBallTM(r, c)
    M = tm_add(tm_add(H, deltaTM(pa, r, c)), tm_mul(r, Wt, symTM(pa, K0, r, c)))
    return tm_trim(P, D, r, M)

def quarterTermQ(t, n):
    a = Q(4 * n + 1, 4)
    return Q(1, n + 1) - a / (a * a + t * t / 4)
def midLower(P, K0, N, a):
    s = Q(0)
    for n in range(K0, N): s += roundQ(P, quarterTermQ(a, n))
    aN = Q(4 * N + 1, 4); T = a * a / 4
    return s - Q(3, 4) * (1 / aN + 1 / aN ** 2) + T / (2 * aN * aN + T)

def shiftPoly(p, h):  # coefficients of s -> p(h + s), Horner
    acc = []
    for a in reversed(p): acc = padd([a], pmul([h, Q(1)], acc))
    return acc

def checkPiece(pa, K0, N, c, r, M, Wp, a, b):
    if not (0 <= a and a <= b and c - r <= a and b <= c + r): return False
    h = (a + b) / 2 - c; rho = (b - a) / 2
    tot = padd(shiftPoly(M[0], h), psmul(midLower(pa[3], K0, N, a), shiftPoly(Wp, h)))
    return M[1] <= floorBound(tot, rho)

def pieceSlack(pa, K0, N, c, r, M, Wp, a, b):
    h = (a + b) / 2 - c; rho = (b - a) / 2
    tot = padd(shiftPoly(M[0], h), psmul(midLower(pa[3], K0, N, a), shiftPoly(Wp, h)))
    return floorBound(tot, rho) - M[1]

# sinc(s/d) at centre 0 on |s| <= r (r <= d): sum_{j<n-1} sinCoef(j+1) (s/d)^j, error (r/d)^(n-1) (n+1)/(n! n)
def sincZeroTM(n, r, d):
    if 1 < n and 0 <= r and r <= d:
        return ([sinCoef(j + 1) / d ** j for j in range(n - 1)], (r / d) ** (n - 1) * Q(n + 1, factorial(n) * n))
    return ([], Q(1))

def wideTM2(pa, K0, hats, r, c):
    q = pa[:4]; P, D, K = pa[3], pa[4], pa[5]
    Wt = (weightPoly(c), Q(0))
    if hats:
        S1 = sincZeroTM(pa[0], r, Q(100)) if c == 0 else sincAffTM(q, K, r, c, Q(100))
        H = tm_smul(Q(2, 50), tm_mul(r, tmPow(r, P, D, S1, 2), hatTM(pa, r, c)))
    else:
        H = hatBallTM(r, c)
    M = tm_add(tm_add(H, deltaTM(pa, r, c)), tm_mul(r, Wt, symTM(pa, K0, r, c)))
    return tm_trim(P, D, r, M)
