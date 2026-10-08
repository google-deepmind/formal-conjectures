#!/usr/bin/env python3
"""Rigorous (Arb ball arithmetic) evaluation of the finite-window Weil functional of a fixed
moment-zero trigonometric test function, for the principal Epstein zeta of x^2 + 5y^2 (D = -20)
and for the same-discriminant Euler control zeta(s) L(s, chi_-20).

Standalone: needs only python-flint (Arb) and the standard library.

Definitions (identical to harness/sdk/epstein_lattice_weil_probe.py, but with no t-truncation):
  g      = sum_i c_i g_{k_i},  g_k = (1/4 - D^2)(sin(pi x/L) sin(k pi x/L))  on [0, L]
         = sum_m C_m cos(m pi x / L)                       (exact, finite cosine polynomial)
  ghat(t)= int_0^L g(x) e^{-itx} dx
  S_F(t) = 2 Re psi(1/2+it) + 2 log(sqrt(20)/(2 pi)) - 2 sum_{log n < L} Lambda_F(n) n^{-1/2} cos(t log n)
  W_F(g) = (1/2pi) int_R |ghat(t)|^2 S_F(t) dt   (= probe's (1/pi) int_0^inf, the probe truncates at T)
  E(g)   = int_0^L g^2 = h(0),       Rayleigh R_F(g) = W_F(g) / E(g)   (the probe's quotient c'Mc / c'Gc)

x-space identity used (rigorous; no frequency tail):
  h(u) := int g(x) g(x+u) dx  (even, continuous, = 0 for |u| >= L),  (1/2pi) int |ghat|^2 cos(tu) dt = h(u).
  Gauss:  Re psi(1/2+it) - psi(1/2) = int_0^inf (1 - cos tu) / (2 sinh(u/2)) du   (integrand >= 0),
  so by Tonelli  (1/2pi) int |ghat|^2 (Re psi(1/2+it) - psi(1/2)) dt = int_0^inf (h(0)-h(u))/(2 sinh(u/2)) du, and
  W_F(g) = h(0) [2 psi(1/2) + 4 artanh(e^{-L/2}) + log(5/pi^2)]
           + int_0^L (h(0) - h(u)) / sinh(u/2) du
           - 2 sum_{log n < L} Lambda_F(n) n^{-1/2} h(log n),        psi(1/2) = -gamma - 2 log 2,
  using int_L^inf du / (2 sinh(u/2)) = 2 artanh(e^{-L/2}).
  The integrand is written as 2 D(u) / sinc(i u/2) with D(u) = (h(0)-h(u))/u expressed through sinc,
  which is analytic on a neighbourhood of [0, L] (poles only at u = 2 pi i k, k != 0), so Arb's
  rigorous Gauss-Legendre/Petras integrator applies directly; no removable-singularity patch needed.

Arithmetic: a(n) = r_Q(n)/2 from exact lattice counts, Lambda_F(n) exactly as rational combinations
of log p via the Dirichlet recurrence a(n) log n = sum_{d|n, d>1} Lambda_F(d) a(n/d).

Usage:
  python3 certify_d20_witness.py                        # the committed 7-mode witness at L = 7/2
  python3 certify_d20_witness.py --witness file.json    # {"L": "p/q", "ks": [...], "c": [...integers...]}
"""
import argparse
import json
import sys
from fractions import Fraction

from flint import acb, arb, ctx, fmpq


# ------------------------------------------------------------------ exact arithmetic
def lattice_counts(nmax, a=1, b=0, c=5):
    r = [0] * (nmax + 1)
    B = int((4 * nmax) ** 0.5) + 3
    for x in range(-B, B + 1):
        for y in range(-B, B + 1):
            v = a * x * x + b * x * y + c * y * y
            if 1 <= v <= nmax:
                r[v] += 1
    return r


def chi_m20(n):
    m4 = 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)
    r5 = n % 5
    c5 = 0 if r5 == 0 else (1 if r5 in (1, 4) else -1)
    return m4 * c5


def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def logder_exact(a):
    lam = [dict() for _ in a]
    for n in range(2, len(a)):
        acc = {}
        if a[n]:
            for p, e in factor(n).items():
                acc[p] = acc.get(p, Fraction(0)) + a[n] * e
        for d in range(2, n):
            if n % d == 0 and a[n // d]:
                for p, cf in lam[d].items():
                    acc[p] = acc.get(p, Fraction(0)) - cf * a[n // d]
        lam[n] = {p: cf for p, cf in acc.items() if cf != 0}
    return lam


def arithmetic_weights(nmax):
    r = lattice_counts(nmax)
    a_pr = [Fraction(0)] + [Fraction(r[n], 2) for n in range(1, nmax + 1)]
    a_eu = [Fraction(0)] + [Fraction(sum(chi_m20(d) for d in range(1, n + 1) if n % d == 0))
                            for n in range(1, nmax + 1)]
    assert a_pr[1] == 1 and a_eu[1] == 1
    return {"principal": logder_exact(a_pr), "euler": logder_exact(a_eu)}


def q(fr):
    return arb(fmpq(fr.numerator, fr.denominator))


def lam_arb(d):
    s = arb(0)
    for p, cf in d.items():
        s += q(cf) * arb(p).log()
    return s


# ------------------------------------------------------------------ the test function
def cosine_coefficients(L, ks, cs):
    """exact-in-Arb cosine coefficients C_m of g = sum c_k (1/4 - D^2)(sin(alpha x) sin(k alpha x))."""
    al = arb.pi() / L
    C = {}
    quarter = arb(1) / 4
    for k, ck in zip(ks, cs):
        C[k - 1] = C.get(k - 1, arb(0)) + arb(ck) * (quarter + ((k - 1) * al) ** 2) / 2
        C[k + 1] = C.get(k + 1, arb(0)) - arb(ck) * (quarter + ((k + 1) * al) ** 2) / 2
    return dict(sorted(C.items())), al


def cross_weights(C):
    """W_m = 2 m^2 C_m sum_{m' != m, m' = m mod 2} C_m' / (m^2 - m'^2)."""
    Wm = {}
    for m, cm in C.items():
        s = arb(0)
        for mp, cmp_ in C.items():
            if mp != m and (m - mp) % 2 == 0:
                s += cmp_ / (m * m - mp * mp)
        Wm[m] = 2 * m * m * cm * s
    return Wm


def h_single(u, L, al, C, Wm):
    """h(u), 0 <= u <= L, single-sum closed form."""
    tot = arb(0)
    for m, cm in C.items():
        if m == 0:
            tot += cm * cm * (L - u)
            continue
        a = m * al
        s, c = (a * u).sin(), (a * u).cos()
        tot += -(Wm[m] / a) * s + cm * cm * ((L - u) * c / 2 - s / (2 * a))
    return tot


def h_double(u, L, al, C):
    """h(u) via the symmetrised pair kernel (independent form, used as a cross-check)."""
    tot = arb(0)
    for m, cm in C.items():
        for mp, cmp_ in C.items():
            if (m + mp) % 2:
                continue
            if m == mp == 0:
                K = L - u
            elif m == mp:
                a = m * al
                K = (L - u) * (a * u).cos() / 2 - (a * u).sin() / (2 * a)
            else:
                a, b = m * al, mp * al
                sa, sb = (a * u).sin(), (b * u).sin()
                K = ((sb - sa) / ((m - mp) * al) - (sa + sb) / ((m + mp) * al)) / 2
            tot += cm * cmp_ * K
    return tot


def D_gap(u, L, al, C, Wm):
    """D(u) = (h(0) - h(u))/u, entire, via sinc; u may be an acb ball."""
    tot = acb(0)
    for m, cm in C.items():
        if m == 0:
            tot += cm * cm
            continue
        a = m * al
        au = a * u
        tot += Wm[m] * au.sinc()
        tot += cm * cm * (L * a * (au / 2).sin() * (au / 2).sinc() / 2 + au.cos() / 2 + au.sinc() / 2)
    return tot


def energy(L, C):
    return sum(((L if m == 0 else L / 2) * cm * cm for m, cm in C.items()), arb(0))


def moment(L, al, C, sign):
    """int_0^L g(x) e^{sign x/2} dx (must be 0 for moment-zero g)."""
    c = arb(sign) / 2
    tot = arb(0)
    for m, cm in C.items():
        beta = m * al
        tot += cm * ((c * L).exp() * (-1) ** m * c - c) / (c * c + beta * beta)
    return tot


# ------------------------------------------------------------------ the certificate
def certify(Lq, ks, cs, prec=160, verbose=True):
    ctx.prec = prec
    L = q(Lq)
    C, al = cosine_coefficients(L, ks, cs)
    Wm = cross_weights(C)
    E = energy(L, C)
    m_plus, m_minus = moment(L, al, C, +1), moment(L, al, C, -1)
    assert m_plus.contains(0) and m_minus.contains(0), "test function is not moment-zero"

    # cross-checks of the closed forms (ball overlap)
    for uq in (Fraction(1, 7), Fraction(3, 2), Lq * Fraction(9, 10)):
        u = q(uq)
        h1, h2 = h_single(u, L, al, C, Wm), h_double(u, L, al, C)
        assert h1.overlaps(h2), ("h forms disagree", uq)
        d1 = D_gap(acb(u), L, al, C, Wm).real
        assert d1.overlaps((E - h1) / u), ("D form disagrees", uq)
    assert h_single(arb(0), L, al, C, Wm).overlaps(E)
    assert abs(h_single(L, L, al, C, Wm)).upper() < (arb("1e-30") * E).upper()

    # Archimedean integral, rigorous
    def integrand(z, analytic):
        return 2 * D_gap(z, L, al, C, Wm) / (z * acb(0, 1) / 2).sinc()

    I = acb.integral(integrand, 0, acb(L), rel_tol=arb(2) ** (-prec // 2 - 20),
                     abs_tol=arb(2) ** (-prec // 2 - 20) * (1 + abs(E.mid())))
    assert I.imag.contains(0)
    I = I.real
    gamma, log2 = arb.const_euler(), arb(2).log()
    psi_half = -gamma - 2 * log2
    const = 2 * psi_half + 4 * (-(L / 2)).exp().atanh() + (arb(5) / arb.pi() ** 2).log()

    # arithmetic support: all n with log n < L (rigorous decision)
    ns = []
    n = 2
    while True:
        ln = arb(n).log()
        if ln < L:
            ns.append(n)
        elif ln > L:
            break
        else:
            raise RuntimeError(f"cannot decide log {n} vs L")
        n += 1
    lam = arithmetic_weights(max(ns) + 1)
    out = {"L": str(Lq), "ks": list(ks), "c": list(cs), "prec_bits": prec,
           "E_h0": E.str(20, radius=True), "const": const.str(20, radius=True),
           "arch_integral": I.str(25, radius=True), "moment_plus": m_plus.str(5, radius=True),
           "moment_minus": m_minus.str(5, radius=True), "n_range": [2, max(ns)]}
    for name in ("principal", "euler"):
        arith = arb(0)
        comp = arb(0)
        terms = {}
        for n in ns:
            if not lam[name][n]:
                continue
            t = 2 * lam_arb(lam[name][n]) / arb(n).sqrt() * h_single(arb(n).log(), L, al, C, Wm)
            arith += t
            if len(factor(n)) > 1:
                comp += t
            terms[n] = t
        Wnum = const * E + I - arith
        R = Wnum / E
        out[name] = {
            "arith_sum": arith.str(25, radius=True),
            "composite_part_of_arith_sum": comp.str(20, radius=True),
            "W_numerator": Wnum.str(25, radius=True),
            "W_numerator_interval": [Wnum.lower().str(22), Wnum.upper().str(22)],
            "rayleigh": R.str(25, radius=True),
            "rayleigh_interval": [R.lower().str(22), R.upper().str(22)],
            "sign": ("NEGATIVE (certified)" if R < 0 else "POSITIVE (certified)" if R > 0 else "UNDECIDED"),
            "lambda_support": {int(k): " + ".join(f"{v}*log{p}" for p, v in sorted(lam[name][k].items()))
                               for k in terms},
        }
    if verbose:
        print(json.dumps(out, indent=1))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--witness", help="JSON with L (fraction string), ks, c (integers)")
    ap.add_argument("--prec", type=int, default=160)
    ap.add_argument("--out")
    args = ap.parse_args()
    if args.witness:
        w = json.load(open(args.witness))
        Lq, ks, cs = Fraction(w["L"]), w["ks"], w["c"]
    else:
        Lq, ks, cs = Fraction(7, 2), (4, 6, 8, 10, 12, 16, 18), (22, 10, 6, 3, 2, -2, -1)
    res = certify(Lq, ks, cs, args.prec)
    if args.out:
        json.dump(res, open(args.out, "w"), indent=1)
    ok = res["principal"]["sign"].startswith("NEGATIVE")
    sys.exit(0 if ok else 1)
