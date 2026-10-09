"""Integer fixed-point (Q.128) outward-rounded interval mirror for the sign of Lambda(1/2 + it).

  Lambda(1/2+it) = Re 2 sum_{n<=3} int_1^X e^{-pi n^2 x} x^{w-1} dx - 1/(1/4+t^2) + E,   w = 1/4 + it/2,
  |E| <= tails (n > 3, x > X) + per-cell Taylor remainders of x^{w-1}.
Every quantity is an interval [lo, hi] of integers meaning [lo, hi] * 2^-P, rounded outward,
so the final enclosure is rigorous given the enclosure lemmas for exp, log, cos, sin and pi.
This is the design the Lean kernel checker will replicate.
"""
import sys
from fractions import Fraction as Fr
P = int(__import__("os").environ.get("FIXP", "128"))
ONE = 1 << P

def fdiv_floor(a, b): return a // b
def fdiv_ceil(a, b): return -((-a) // b)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi=None):
        self.lo, self.hi = lo, (lo if hi is None else hi)
        assert self.lo <= self.hi
    @staticmethod
    def of(q):                       # rational -> enclosing interval
        q = Fr(q); return I(fdiv_floor(q.numerator * ONE, q.denominator), fdiv_ceil(q.numerator * ONE, q.denominator))
    def __add__(s, o): o = o if isinstance(o, I) else I.of(o); return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o): return s + (-(o if isinstance(o, I) else I.of(o)))
    def __rsub__(s, o): return I.of(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, I) else I.of(o)
        ps = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(fdiv_floor(min(ps), ONE), fdiv_ceil(max(ps), ONE))
    __rmul__ = __mul__
    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return I(fdiv_floor(ONE * ONE, s.hi), fdiv_ceil(ONE * ONE, s.lo))
    def __truediv__(s, o): return s * (o if isinstance(o, I) else I.of(o)).inv()
    def mag(s): return max(abs(s.lo), abs(s.hi))           # |x| <= mag * 2^-P
    def widen(s, e): return I(s.lo - e, s.hi + e)          # add +-e (units 2^-P)
    def f(s): return (s.lo / ONE, s.hi / ONE)

def err_units(q): return fdiv_ceil(Fr(q).numerator * ONE, Fr(q).denominator)

# pi: Mathlib Real.pi_gt_d20 / pi_lt_d20
PI = I(fdiv_floor(314159265358979323846 * ONE, 10**20), fdiv_ceil(314159265358979323847 * ONE, 10**20))

def exp_small(x, n=40):
    """|x| <= 1/2: Taylor + Lagrange bound |R| <= |x|^n/n! * 2."""
    s, term = I.of(1), I.of(1)
    for k in range(1, n):
        term = term * x / k; s = s + term
    m = Fr(x.mag(), ONE); return s.widen(err_units(2 * m**n / __import__('math').factorial(n)))

def exp_(x):
    r = 0
    while Fr(x.mag(), ONE) > Fr(1, 2): x = x * Fr(1, 2); r += 1
    y = exp_small(x)
    for _ in range(r): y = y * y
    return y

def log_(c):
    """c rational >= 1: log c = 2 sum z^(2k+1)/(2k+1), z = (c-1)/(c+1); tail <= 2 z^(2n+1)/((2n+1)(1-z^2))."""
    z = Fr(c - 1, 1) / (c + 1); zi = I.of(z); s = I.of(0); p = zi; n = 0
    while True:
        s = s + p * Fr(2, 2 * n + 1); n += 1; p = p * zi * zi
        tail = 2 * z ** (2 * n + 1) / ((2 * n + 1) * (1 - z * z))
        if tail < Fr(1, 2 ** (P + 4)): return s.widen(err_units(tail) + 1)

def cos_sin(x):
    """cos and sin of an interval x via halving + double angle; |R| from Taylor of exp(ix)."""
    r = 0
    while Fr(x.mag(), ONE) > Fr(1, 4): x = x * Fr(1, 2); r += 1
    c, s, term = I.of(1), I.of(0), I.of(1)
    for k in range(1, 40):
        term = term * x / k
        if k % 4 == 1: s = s + term
        elif k % 4 == 2: c = c - term
        elif k % 4 == 3: s = s - term
        else: c = c + term
    e = err_units(2 * Fr(x.mag(), ONE) ** 40 / __import__('math').factorial(40)) + 1
    c, s = c.widen(e), s.widen(e)
    for _ in range(r): c, s = c * c - s * s, 2 * c * s
    return c, s

class C:                               # complex rectangle
    def __init__(s, re, im): s.re, s.im = re, im
    def __add__(s, o): return C(s.re + o.re, s.im + o.im)
    def __mul__(s, o):
        if isinstance(o, C): return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
        return C(s.re * o, s.im * o)
    def widen(s, e): return C(s.re.widen(e), s.im.widen(e))

def binom_abs_bound(wr, wi, k):         # |binom(w-1, k)| upper bound, w-1 = wr + i wi (rational)
    b = Fr(1)
    for j in range(k):
        q = (wr - j) ** 2 + wi ** 2                        # |w-1-j| <= ceil(sqrt(q * 10^24)) / 10^12
        num = q.numerator * 10**24; den = q.denominator
        r = __import__('math').isqrt(num // den) + 1
        b *= Fr(r, 10**12) / (j + 1)
    return b

def lam(t, X=12, h=Fr(1, 4), d=12, nmax=3):
    t = Fr(t); wr, wi = Fr(-3, 4), t / 2                    # w - 1
    total = C(I.of(0), I.of(0)); rem = Fr(0)
    a = Fr(1)
    exps = {}
    def e_ax(n, x):                                         # e^{-pi n^2 x}
        key = (n, x)
        if key not in exps: exps[key] = exp_(-(PI * (n * n)) * x)
        return exps[key]
    while a < X:
        b = a + h; c = a + h / 2
        lc = log_(c)
        cr, ci = cos_sin(lc * wi)                           # e^{i (t/2) log c}
        base = exp_(lc * wr)                                 # c^{-3/4}
        # coefficients C_k = binom(w-1, k) c^{w-1-k}
        coef = []; bin_ = C(I.of(1), I.of(0)); ck = C(base * cr, base * ci)
        for k in range(d + 1):
            coef.append(bin_ * ck)
            bin_ = bin_ * C(I.of(wr - k), I.of(wi)) * I.of(Fr(1, k + 1))
            ck = ck * I.of(1 / c)
        # Taylor remainder bound of x^{w-1} on the cell
        Rk = binom_abs_bound(wr, wi, d + 1) * a ** 0 * (h / 2) ** (d + 1)  # times max x^{-3/4-d-1} <= a^{-3/4-d-1} <= 1/a^(d+1)
        Rk = Rk / a ** (d + 1)
        for n in range(1, nmax + 1):
            al = PI * (n * n)
            ea, eb = e_ax(n, a), e_ax(n, b)
            # I_k = int_a^b e^{-al x}(x-c)^k dx;  I_0 = (ea - eb)/al;  I_k = (ea (a-c)^k - eb (b-c)^k)/al + k/al I_{k-1}
            Ik = (ea - eb) / al; acc = coef[0] * Ik
            for k in range(1, d + 1):
                Ik = (ea * I.of((a - c) ** k) - eb * I.of((b - c) ** k)) / al + Ik * I.of(k) / al
                acc = acc + coef[k] * Ik
            total = total + acc * I.of(2)
            # remainder: 2 * Rk * int_a^b e^{-al x} dx  <= 2 Rk (b-a) e^{-al a}, with e^{-al a} <= e^{-3 n^2 a}
            rem += 2 * Rk * h * Fr(ea.hi, ONE)
        a = b
    tail_n = Fr(2) * Fr(e_ax(nmax + 1, Fr(1)).hi, ONE) * 2                     # n > nmax  (geometric, ratio <= e^{-pi})
    tail_x = sum(Fr(2) * Fr(e_ax(n, Fr(X)).hi, ONE) / 3 for n in range(1, nmax + 1))  # x > X, |x^{w-1}| <= 1, alpha >= 3
    E = rem + tail_n + tail_x
    val = total.re - I.of(1 / (Fr(1, 4) + t * t))
    return val.widen(err_units(E)), E

if __name__ == '__main__':
    for t in sys.argv[1:]:
        v, E = lam(Fr(t))
        lo, hi = v.f()
        sign = '+' if v.lo > 0 else ('-' if v.hi < 0 else '?')
        print(f't={t}: Lambda in [{lo:.12e}, {hi:.12e}]  width {hi-lo:.2e}  analytic error {float(E):.2e}  sign {sign}', flush=True)
