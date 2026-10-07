# Rigorous ball-arithmetic (Arb, via python-flint) check of every cell of the
# order-19 L = 4/5 Krein certificate:
#
#   correctionSymbol(t) + W(t) * (S(t) - 1/16) - W(t) * lv  >=  0   on [lo, hi],
#   W(t) = (t^2 + 1/4)^2,
#
# with S one of
#   exact : symbol(t) = Re psi(1/4 + i t/2) - log pi - sqrt2 log2 cos(t log2)
#   lean  : the lower bound assembled only from facts already proved in the
#           Lean tree (RHKreinDigammaLowerBoundV1 / ...MonotonicityV1, gamma < 0.5773,
#           log pi upper, |log 2 - 287209/414355| <= 1e-10):
#             -5773/10000 + sum_{n<128} quarterTerm(lo, n)
#               - (3/4) (1/(128+1/4) + 1/(128+1/4)^2) - 1144729886/10^9
#               - A0 cos(t L0) - A0 t 10^-10 - 2*10^-9,
#           A0 = 1414213562/10^9 * 6931471806/10^10, L0 = 287209/414355.
#
# Each cell is enclosed by a degree-K Taylor model about its centre (coefficients
# 0..K-1 at the exact centre, coefficient K enclosed over the whole cell) and the
# sign-independent floor a_0 - sum_k |a_k| r^k; undecided cells are bisected.
#
# usage: KREIN_CERT=certificate.json EXPLICIT_CORRECTION=RHKreinExplicitCorrectionV1.lean \
#        python3 arb_cells.py {exact|lean} [first last]
import json, os, re, sys
from fractions import Fraction as F
from flint import arb, acb, arb_series, acb_series, ctx

ctx.prec = 256
K = 8
MODE = sys.argv[1]
src = open(os.environ['EXPLICIT_CORRECTION']).read()
blk = src[src.index('def hatCoefficient'):src.index('def splineCoefficient')]
def q(x): x = F(x); return arb(x.numerator) / x.denominator
HC = [q(x) for x in re.findall(r'(-?\d+(?:/\d+)?)', blk.split('![')[1])]
SP = [q(F(234102120892757, 5000000000)), q(F(-12240399939171, 2500000000)),
      q(F(-2918648959121, 10000000000)), q(F(123578990441, 10000000000)),
      q(F(9711997751, 10000000000))]
H = [arb(j + 41) / 50 for j in range(199)]
WF = arb(1619) / 2000
LN2 = arb(2).log(); SQ2 = arb(2).sqrt(); LOGPI = arb.pi().log()
L0 = arb(287209) / 414355; E2 = arb(1) / 10**10
A0 = q(F(1414213562, 10**9)) * q(F(6931471806, 10**10)); DA = arb(2) / 10**9

def correction_and_weight(x, n):
    hat = arb_series([0], n)
    for c, h in zip(HC, H):
        hat += c * (x * h).cos()
    sw, cw = (x * WF).sin_cos()
    E = arb_series([0], n); xp = arb_series([1], n)
    for j, s in enumerate(SP):
        E += s * xp * (cw if j % 2 == 0 else sw); xp = xp * x
    def sinc(y): return y.sin() * y.inv()
    f = arb(2) / 50 * sinc(x / 100) ** 2 * hat + sinc(x / 2000) ** 19 * E
    return f, (x * x + arb(1) / 4) ** 2

def exact_symbol(t0, n):
    x = arb_series([t0, 1], n)
    z = acb_series([acb(arb(1) / 4, t0 / 2), acb(0, arb(1) / 2)], n + 1)
    dl = z.lgamma().derivative()
    psi = [(dl.coeffs()[k] / acb(0, arb(1) / 2)).real for k in range(n)]
    return arb_series(psi, n) - LOGPI - SQ2 * LN2 * (x * LN2).cos()

def lean_arch_floor(lo, N=128):
    s = sum(1 / arb(n + 1) - (arb(n) + arb(1) / 4) / ((arb(n) + arb(1) / 4) ** 2 + lo * lo / 4)
            for n in range(N))
    NN = arb(N) + arb(1) / 4
    return arb(-5773) / 10000 + s - arb(3) / 4 * (1 / NN + 1 / NN ** 2) - arb(1144729886) / 10**9

def floor(lo, hi, lv, arch_lo):
    c = (lo + hi) / 2; r = (hi - lo) / 2; out = []
    for t0, n in ((c, K), (arb(c, r), K + 1)):
        x = arb_series([t0, 1], n)
        f, W = correction_and_weight(x, n)
        if MODE == 'exact':
            S = exact_symbol(t0, n)
        else:
            S = arch_lo - A0 * (x * L0).cos() - A0 * x * E2 - DA
        out.append((f + W * (S - arb(1) / 16) - W * lv).coeffs())
    a = out[0][:K] + [out[1][K]]
    fl = a[0]
    for k in range(1, K + 1):
        fl -= abs(a[k]) * r ** k
    return fl, a[0]

def decide(lo, hi, lv, arch_lo, depth=0):
    fl, a0 = floor(lo, hi, lv, arch_lo)
    if fl > 0: return 'POS', 1, fl
    if a0 < 0: return 'NEG', 1, a0
    if depth >= 24: return 'UNDECIDED', 1, fl
    m = (lo + hi) / 2
    r1 = decide(lo, m, lv, arch_lo, depth + 1)
    if r1[0] != 'POS': return r1
    r2 = decide(m, hi, lv, arch_lo, depth + 1)
    if r2[0] != 'POS': return r2
    return 'POS', r1[1] + r2[1], min(r1[2], r2[2], key=lambda b: b.lower())

cells = json.load(open(os.environ['KREIN_CERT']))['accepted_intervals']
first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
last = int(sys.argv[3]) if len(sys.argv) > 3 else len(cells) - 1
counts = {}
total = 0
for i in range(first, last + 1):
    lo, hi = q(cells[i][0]), q(cells[i][1]); lv = arb(cells[i][2]) / arb(2) ** 64
    st, pieces, fl = decide(lo, hi, lv, lean_arch_floor(lo) if MODE == 'lean' else None)
    counts[st] = counts.get(st, 0) + 1; total += pieces
    print(i, cells[i][0], cells[i][1], st, pieces, '%.6e' % float(fl.lower()), flush=True)
print('#', MODE, counts, 'pieces', total)
