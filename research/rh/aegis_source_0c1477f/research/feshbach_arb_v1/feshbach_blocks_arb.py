"""Rigorous (Arb) A11, G11 and C_B >= ||P_perp A v||^2 on V = moment-zero part of span{e_m : |m|<=N}.
Rows of the cutoff-free CvS matrix for |n| <= NP are evaluated in Arb; |n| > NP by an explicit 1/n tail bound."""
import sys, math, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
from flint import arb, acb, arb_mat, acb_mat, ctx
import cvs_entries as gw
ctx.prec = 192
L = arb(sys.argv[1]); N = int(sys.argv[2]); NP = int(sys.argv[3])
pi = arb.pi(); quarter = arb('0.25'); psi_q = quarter.digamma()
def seqs(n):
    omega = 2 * pi * n / L; z = acb(quarter, pi * n / L)
    psi = z.digamma(); g_s, g_cc, g_x1, g_x2 = gw._geometric_remainders(n, L, ctx.prec)
    S = arb('0.5') * psi.imag - omega * g_s if n else arb(0)
    CC = -arb('0.5') * (psi.real - psi_q) + g_cc if n else arb(0)
    XC = arb('0.25') * z.polygamma(acb(1)).real - L * g_x1 - g_x2
    return S, CC, XC
cmax = int(math.exp(float(L.mid())))
primes = [(q, p) for q, p in gw.prime_powers_up_to(max(cmax, 2)) if arb(q).log() < L]
W = [arb(p).log() * arb(q) ** arb('-0.5') for q, p in primes]; Y = [arb(q).log() for q, _ in primes]
beta = L / (4 * pi); Cc = L * ((L.exp()).sqrt() + 1 / (L.exp()).sqrt() - 2) / (2 * pi * pi)
kappa = gw._kappa(L); jc = gw._J(L)
band = list(range(-N, N + 1))
Sb = {m: seqs(abs(m)) for m in band}
sS = lambda m, Sm: Sm if m >= 0 else -Sm
def entry(n, m, Sn_signed, CCn, XCn):
    pole = Cc * (beta * beta - n * m) / ((n * n + beta * beta) * (m * m + beta * beta))
    if n == m:
        wr = kappa + 2 * CCn + jc - (2 / L) * XCn
        wp = sum((w * 2 * (1 - y / L) * (2 * pi * n * y / L).cos() for w, y in zip(W, Y)), arb(0))
    else:
        wr = (sS(m, Sb[m][0]) - Sn_signed) / (pi * (n - m))
        wp = sum((w * ((2 * pi * m * y / L).sin() - (2 * pi * n * y / L).sin()) / (pi * (n - m)) for w, y in zip(W, Y)), arb(0))
    return pole - wr - wp
# moment-zero basis Z (complex): constraints sum_m u_m mu_s(m) = 0, s = +-1/2
def mom(m, s):
    a = acb(s, 2 * pi * m / L); return ((a * L).exp() - 1) / a
piv = [0, 1]; rest = [m for m in band if m not in piv]
Cp = acb_mat([[mom(m, s) for m in piv] for s in (arb('0.5'), arb('-0.5'))])
Cpinv = Cp.inv()
Z = acb_mat(2 * N + 1, len(rest))
for j, m in enumerate(rest):
    Z[band.index(m), j] = 1
    rhs = acb_mat([[-mom(m, arb('0.5'))], [-mom(m, arb('-0.5'))]]); sol = Cpinv * rhs
    for t, p in enumerate(piv): Z[band.index(p), j] = sol[t, 0]
k = len(rest)
# rows |n| <= NP
R = arb_mat(2 * NP + 1, 2 * N + 1)
for i, n in enumerate(range(-NP, NP + 1)):
    Sn, CCn, XCn = Sb[n] if n in Sb else seqs(abs(n))
    Sns = sS(n, Sn)
    for j, m in enumerate(band):
        R[i, j] = entry(n, m, Sns, CCn, XCn)
    if i % 2000 == 0: print("row", n, flush=True)
Qb = acb_mat(arb_mat([[R[NP + n, band.index(m)] for m in band] for n in band]))
RR = acb_mat(R.transpose() * R)
# tail |n| > NP.  With 1/(n-m) = 1/n + m/(n(n-m)) and v supported on |m| <= N:
#   (Qv)_n = l1(v)/(pi n) + (sS(n) + sum_q w_q sin th_n) l0(v)/(pi n) + pole_n(v) + E_n,
#   l1 = sum_m alpha_m v_m, alpha_m = -(sS(m) + sum_q w_q sin th_m), l0 = sum_m v_m,
#   |pole_n(v)| <= Cc |lb(v)|/|n| + Cc beta^2 |la(v)|/n^2   (la, lb: pole functionals),
#   |E_n| <= (Amax + K2) N ||v||_1 / (pi |n| (|n| - N)),   K2 >= |S[n]| + sum_q w_q for |n| > NP.
# Cauchy-Schwarz over the five terms and sum_{|n|>NP} n^-2 <= 2/NP give the PSD bound Tail + Eco*I below.
KS = arb(0)
for kk in range(200):
    ck = 2 * kk + arb('0.5'); KS += (-ck * L).exp() / (2 * ck)
ymin = pi * NP / L
K2 = pi / 4 + 1 / (2 * ymin) + KS + sum(W, arb(0))   # |S[n]| <= pi/4 + 1/(2y) + KS for |n| > NP
alpha = [-(sS(m, Sb[m][0]) + sum((w * (2 * pi * m * y / L).sin() for w, y in zip(W, Y)), arb(0))) for m in band]
avec = [1 / (m * m + beta * beta) for m in band]; bvec = [m / (m * m + beta * beta) for m in band]
def outer(v): return acb_mat([[acb(v[i]) * acb(v[j]) for j in range(len(v))] for i in range(len(v))])
c1 = 10 / (pi * pi * NP)
Tail = outer(alpha) * c1 + outer([arb(1)] * len(band)) * (c1 * K2 * K2) + outer(bvec) * (c1 * pi * pi * Cc * Cc) \
     + outer(avec) * (c1 * pi * pi * Cc * Cc * beta ** 4 / (NP * NP))
Amax = max(abs(a_) for a_ in alpha).upper()
Eco = 10 * (Amax + K2) ** 2 * N * N * (2 * N + 1) / (3 * pi * pi * arb(NP - N) ** 3)
print('K2', K2, 'Amax', Amax, 'Eco', Eco)
Ib = acb_mat(2 * N + 1, 2 * N + 1)
for i in range(2 * N + 1): Ib[i, i] = Eco
Zh = Z.conjugate().transpose()
A11 = Zh * Qb * Z; G11 = Zh * Z
CB = Zh * (RR + Tail + Ib) * Z - A11 * G11.inv() * A11
def mid(M): return [[complex(float(M[i, j].real.mid()), float(M[i, j].imag.mid())) for j in range(M.ncols())] for i in range(M.nrows())]
blocks = {"L": str(L), "N": N, "NP": NP, "K2": K2.str(30), "Amax": Amax.str(30), "tail_coef": c1.str(30), "Eco": Eco.str(30),
          "A11": [[(A11[i, j].real.str(40), A11[i, j].imag.str(40)) for j in range(k)] for i in range(k)],
          "G11": [[(G11[i, j].real.str(40), G11[i, j].imag.str(40)) for j in range(k)] for i in range(k)],
          "CB": [[(CB[i, j].real.str(40), CB[i, j].imag.str(40)) for j in range(k)] for i in range(k)]}
json.dump(blocks, open(f"blocks_N{N}_NP{NP}.json", "w"), indent=0)
import numpy as np
A = np.array(mid(A11)); G = np.array(mid(G11)); C = np.array(mid(CB))
from scipy.linalg import eigh
ev, U = eigh(A, G); print("A11 gen eig:", ev[:4])
u0 = U[:, 0]; print("C_B on bottom:", (u0.conj() @ C @ u0).real)
print("max radius A11:", max(float(A11[i, j].real.rad()) for i in range(k) for j in range(k)),
      " CB:", max(float(CB[i, j].real.rad()) for i in range(k) for j in range(k)))
