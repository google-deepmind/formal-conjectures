# Exact Fraction mirror of RHKreinTaylorModelV1 / RHKreinTrigTMV1 / RHKreinCellCheckerV1.
import math, re, os
from fractions import Fraction as F
from math import factorial, floor, ceil

def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def psmul(c, p): return [c * a for a in p]
def pmul(p, q):
    if not p: return []
    out = [F(0)] * (len(p) + len(q) - 1) if q else [F(0)] * len(p)
    # Lean: pmul (a::p) q = padd (psmul a q) (0 :: pmul p q); length = len(p)+len(q)-1 when q nonempty,
    # and when q empty: padd [] (0 :: ...) gives zeros of length len(p).
    if not q:
        return [F(0)] * len(p)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out
def absBound(p, r):
    acc = F(0)
    for a in reversed(p): acc = abs(a) + r * acc
    return acc
def floorBound(p, r):
    if not p: return F(0)
    return p[0] - r * absBound(p[1:], r)
def roundQ(k, q): return F(floor(q * 2 ** k), 2 ** k)
def roundUpQ(k, q): return F(ceil(q * 2 ** k), 2 ** k)

class TM:
    __slots__ = ('p', 'e')
    def __init__(s, p, e): s.p = p; s.e = e
def const(a): return TM([F(a)], F(0))
def ball(a, e): return TM([a], e)
def tadd(T, U): return TM(padd(T.p, U.p), T.e + U.e)
def tneg(T): return TM(psmul(F(-1), T.p), T.e)
def tsub(T, U): return tadd(T, tneg(U))
def tsmul(c, T): return TM(psmul(c, T.p), abs(c) * T.e)
def tmul(r, T, U):
    return TM(pmul(T.p, U.p), T.e * absBound(U.p, r) + absBound(T.p, r) * U.e + T.e * U.e)
def trim(k, n, r, T):
    q = [roundQ(k, a) for a in T.p[:n]]
    return TM(q, roundUpQ(k, T.e + absBound(padd(T.p, psmul(F(-1), q)), r)))

def cosCoef(m): return F((-1) ** (m // 2), factorial(m)) if m % 2 == 0 else F(0)
def sinCoef(m): return F((-1) ** (m // 2), factorial(m)) if m % 2 == 1 else F(0)
def coefFrom(f, h, k, n): return [f(k + i) * h ** (k + i) for i in range(n)]
def taylorErr(n, x): return x ** n * (F(n + 1) / (factorial(n) * n))
def cosScaled(n, r, h):
    if 0 < n and 0 <= r and r * abs(h) <= 1: return TM(coefFrom(cosCoef, h, 0, n), taylorErr(n, r * abs(h)))
    return TM([], F(1))
def sinScaled(n, r, h):
    if 0 < n and 0 <= r and r * abs(h) <= 1: return TM(coefFrom(sinCoef, h, 0, n), taylorErr(n, r * abs(h)))
    return TM([], F(1))
def evalQ(p, x):
    acc = F(0)
    for a in reversed(p): acc = a + x * acc
    return acc
def baseCS(n, P, x):
    c = evalQ(coefFrom(cosCoef, F(1), 0, n), x); s = evalQ(coefFrom(sinCoef, F(1), 0, n), x)
    return (roundQ(P, c), roundQ(P, s), roundUpQ(P, taylorErr(n, abs(x)) + F(1, 2 ** P)))
def dbl(P, A):
    c, s, e = A
    return (roundQ(P, c * c - s * s), roundQ(P, 2 * c * s), roundUpQ(P, 2 * e * (2 + e) + F(1, 2 ** P)))
def cosSin(n, k, P, a):
    x = a / 2 ** k
    if 0 < n and abs(x) <= 1:
        A = baseCS(n, P, x)
        for _ in range(k): A = dbl(P, A)
        return A
    return (F(0), F(0), F(1))

class Q:
    def __init__(s, n, nb, k, P): s.n, s.nb, s.k, s.P = n, nb, k, P
def cosAff(q, r, c, h):
    A = cosSin(q.nb, q.k, q.P, c * h)
    return tsub(tmul(r, ball(A[0], A[2]), cosScaled(q.n, r, h)), tmul(r, ball(A[1], A[2]), sinScaled(q.n, r, h)))
def sinAff(q, r, c, h):
    A = cosSin(q.nb, q.k, q.P, c * h)
    return tadd(tmul(r, ball(A[1], A[2]), cosScaled(q.n, r, h)), tmul(r, ball(A[0], A[2]), sinScaled(q.n, r, h)))
def invTM(K, r, c):
    return TM(coefFrom(lambda k: F((-1) ** k) / c ** (k + 1), F(1), 0, K), r ** K / (c ** K * (c - r)))
def sincAff(q, K, r, c, d):
    if 0 <= r and r < c and 0 < d:
        return tmul(r, sinAff(q, r, c, F(1) / d), tsmul(d, invTM(K, r, c)))
    return TM([], F(1))
def tmPow(r, P, D, T, m):
    R = const(1)
    for _ in range(m): R = trim(P, D, r, tmul(r, R, T))
    return R

src = open(os.environ.get('EXPLICIT_CORRECTION',
    '/home/user/mathlib4-433/tree_cell2/AEGISOverlay/RHKreinExplicitCorrectionV1.lean')).read()
blk = src[src.index('def hatCoefficient'):src.index('def splineCoefficient')]
HC = [F(x) for x in re.findall(r'(-?\d+(?:/\d+)?)', blk.split('![')[1])]
assert len(HC) == 199
SP = [F(234102120892757, 5000000000), F(-12240399939171, 2500000000), F(-2918648959121, 10000000000),
      F(123578990441, 10000000000), F(9711997751, 10000000000)]

class PA:
    def __init__(s, q, K, P, D): s.q, s.K, s.P, s.D = q, K, P, D
def hatTM(pa, r, c, N):
    T = const(0)
    for n in range(N):
        T = trim(pa.P, pa.D, r, tadd(T, tsmul(HC[n], cosAff(pa.q, r, c, F(n + 41, 50)))))
    return T
def tVar(c): return TM([c, F(1)], F(0))
def edgeTM(pa, r, c):
    C = cosAff(pa.q, r, c, F(1619, 2000)); S = sinAff(pa.q, r, c, F(1619, 2000))
    T = tVar(c); T2 = tmul(r, T, T); T3 = tmul(r, T2, T); T4 = tmul(r, T2, T2)
    X = tadd(tadd(tadd(tadd(tsmul(SP[0], C), tsmul(SP[1], tmul(r, T, S))), tsmul(SP[2], tmul(r, T2, C))),
                   tsmul(SP[3], tmul(r, T3, S))), tsmul(SP[4], tmul(r, T4, C)))
    return trim(pa.P, pa.D, r, X)
def weightTM(r, c):
    T = tVar(c); B = tadd(tmul(r, T, T), const(F(1, 4))); return tmul(r, B, B)
def quarterTermQ(t, n): return F(1, n + 1) - (n + F(1, 4)) / ((n + F(1, 4)) ** 2 + t * t / 4)
def archLQ(lo):
    s = sum((quarterTermQ(lo, n) for n in range(128)), F(0))
    return F(-5773, 10000) + s - F(3, 4) * (1 / (128 + F(1, 4)) + 1 / (128 + F(1, 4)) ** 2) - F(1144729886, 1000000000)
A0 = F(1414213562, 1000000000) * F(6931471806, 10000000000)
L0 = F(287209, 414355)
def slackTM(pa, r, c, lo, lv, arch=None):
    a = archLQ(lo) if arch is None else arch
    return tsub(tsub(const(a - F(1, 16) - lv - F(2, 10 ** 9)), tsmul(A0, cosAff(pa.q, r, c, L0))),
                tsmul(A0 / 10 ** 10, tVar(c)))
def marginTM(pa, lo, lv, a, b, arch=None):
    c = (a + b) / 2; r = (b - a) / 2
    S1 = sincAff(pa.q, pa.K, r, c, F(100)); S2 = sincAff(pa.q, pa.K, r, c, F(2000))
    corr = tadd(tsmul(F(2, 50), tmul(r, tmPow(r, pa.P, pa.D, S1, 2), hatTM(pa, r, c, 199))),
                tmul(r, tmPow(r, pa.P, pa.D, S2, 19), edgeTM(pa, r, c)))
    return tadd(corr, tmul(r, weightTM(r, c), slackTM(pa, r, c, lo, lv, arch)))
def checkPiece(pa, lo, lv, a, b, arch=None):
    if not (0 < lo and lo <= a and a <= b): return False, None
    M = marginTM(pa, lo, lv, a, b, arch)
    return M.e <= floorBound(M.p, (b - a) / 2), (M.e, floorBound(M.p, (b - a) / 2), len(M.p))

# ---- rotation-based hat sum (RHKreinRotTMV1) ----
def baseZ(n, P, x):
    return (roundQ(P, evalQ(coefFrom(cosCoef, F(1), 0, n), x)), roundQ(P, evalQ(coefFrom(sinCoef, F(1), 0, n), x)),
            roundUpQ(P, taylorErr(n, abs(x)) + F(2, 2 ** P)))
def rotC(P, A, B):
    return (roundQ(P, A[0] * B[0] - A[1] * B[1]), roundQ(P, A[0] * B[1] + A[1] * B[0]),
            roundUpQ(P, A[2] + (1 + A[2]) * B[2] + F(2, 2 ** P)))
def phaseZ(n, k, P, a):
    x = a / 2 ** k
    if 0 < n and abs(x) <= 1:
        A = baseZ(n, P, x)
        for _ in range(k): A = rotC(P, A, A)
        return A
    return (F(0), F(0), F(1))
def cosFrom(n, r, h, A):
    return tsub(tmul(r, ball(A[0], A[2]), cosScaled(n, r, h)), tmul(r, ball(A[1], A[2]), sinScaled(n, r, h)))
def hatTM(pa, r, c, N):
    A = phaseZ(pa.q.nb, pa.q.k, pa.P, c * F(41, 50)); B = phaseZ(pa.q.nb, pa.q.k, pa.P, c / 50)
    T = const(0)
    for n in range(N):
        T = trim(pa.P, pa.D, r, tadd(T, tsmul(HC[n], cosFrom(pa.q.n, r, F(n + 41, 50), A))))
        A = rotC(pa.P, A, B)
    return T

# ---- fast hat (RHKreinHatFastV1) and pow19 ----
def sigma(m, C, S):
    return F((-1) ** (m // 2)) * C if m % 2 == 0 else -(F((-1) ** (m // 2)) * S)
def phaseRow(C, S, h, n):
    out = []; t = F(1)
    for k in range(n):
        out.append(sigma(k, C, S) * t); t = t * h / (k + 1)
    return out
def colErr(n, r, h, A): return A[2] + (1 + A[2]) * taylorErr(n, r * abs(h))
def hatTM(pa, r, c, N):
    A = phaseZ(pa.q.nb, pa.q.k, pa.P, c * F(41, 50)); B = phaseZ(pa.q.nb, pa.q.k, pa.P, c / 50)
    p = []; e = F(0)
    for n in range(N):
        h = F(n + 41, 50)
        if 0 < pa.q.n and r * abs(h) <= 1:
            p = padd(p, psmul(HC[n], phaseRow(A[0], A[1], h, pa.q.n))); e = e + abs(HC[n]) * colErr(pa.q.n, r, h, A)
        else:
            e = e + abs(HC[n])
        A = rotC(pa.P, A, B)
    return trim(pa.P, pa.D, r, TM(p, e))
def tmSq(r, P, D, T): return trim(P, D, r, tmul(r, T, T))
def pow19(r, P, D, T):
    T2 = tmSq(r, P, D, T); T4 = tmSq(r, P, D, T2); T8 = tmSq(r, P, D, T4); T16 = tmSq(r, P, D, T8)
    return trim(P, D, r, tmul(r, trim(P, D, r, tmul(r, T16, T2)), T))
def marginTM(pa, lo, lv, a, b, arch=None):
    c = (a + b) / 2; r = (b - a) / 2
    S1 = sincAff(pa.q, pa.K, r, c, F(100)); S2 = sincAff(pa.q, pa.K, r, c, F(2000))
    corr = tadd(tsmul(F(2, 50), tmul(r, tmPow(r, pa.P, pa.D, S1, 2), hatTM(pa, r, c, 199))),
                tmul(r, pow19(r, pa.P, pa.D, S2), edgeTM(pa, r, c)))
    return tadd(corr, tmul(r, weightTM(r, c), slackTM(pa, r, c, lo, lv, arch)))
