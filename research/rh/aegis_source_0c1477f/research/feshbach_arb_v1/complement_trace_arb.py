"""Rigorous upper bound for tr(P T P), P = projection onto H (-) V in L^2[0,L],
T = P_L M_sbar P_L (sbar = certified step slack).  tr(PTP) = tr T - tr(Pi T), Pi onto V (+) span(e^{+-x/2}).
tr(Pi T) = tr(G^{-1} B^* M1 B) with M1 = Gauss-Legendre (Arb) + Bernstein-ellipse error balls."""
import sys, json, math, os
from flint import arb, acb, arb_mat, acb_mat, ctx
ctx.prec = 192
L = arb(sys.argv[1]); N = int(sys.argv[2]); SB = json.load(open(sys.argv[3])); NG = 24; RHO = arb(4)
Z0 = arb(SB['z0']); STEP = arb(SB['step']); SBAR = [arb(v) for v in SB['sbar']]
pi = arb.pi(); sqL = L.sqrt(); I = acb(0, 1)
band = list(range(-N, N + 1)); om = {n: 2 * pi * n / L for n in band}
def g(z):
    if abs(z.mid()) + z.rad() < arb('0.25'):
        K = 40; t = acb(1); s = acb(0); fk = arb(1)
        for k in range(K):
            fk = fk * (k + 1)
            s += t * L ** (k + 1) / fk; t = t * z
        s += acb(0) + acb(arb(0, 2 * (L ** (K + 2)) * (abs(z).upper()) ** K / (fk * (K + 1))), arb(0, 2 * (L ** (K + 2)) * (abs(z).upper()) ** K / (fk * (K + 1))))
        return s
    return ((z * L).exp() - 1) / z
def hats(xi):
    h = [g(I * (xi + om[n])) / sqL for n in band] + [g(arb('0.5') + I * xi), g(arb('-0.5') + I * xi)]
    hs = [g(-I * (xi + om[n])) / sqL for n in band] + [g(arb('0.5') - I * xi), g(arb('-0.5') - I * xi)]
    return h, hs
nodes = [arb.legendre_p_root(NG, k, weight=True) for k in range(NG)]
D = 2 * N + 3
M1 = acb_mat(D, D); errtot = arb(0)
for j, sb in enumerate(SBAR):
    if not sb > 0: continue
    a = Z0 + j * STEP; b = a + STEP; half = STEP / 2
    eta = half * (RHO - 1 / RHO) / 2
    Mb = L * L * ((arb('0.5') + eta) * L * 2).exp()
    err = half * 64 * Mb / (15 * (RHO * RHO - 1) * RHO ** (2 * NG))
    for sign in (1, -1):
        Hs = acb_mat(D, NG); Hb = acb_mat(NG, D)
        for k, (t, w) in enumerate(nodes):
            xi = sign * ((a + b) / 2 + half * t)
            h, hs = hats(xi)
            for r in range(D):
                Hs[r, k] = hs[r] * (w * half * sb / (2 * pi)); Hb[k, r] = h[r]
        M1 += Hs * Hb
        errtot += sb / (2 * pi) * err
for r in range(D):
    for c in range(D):
        M1[r, c] += acb(arb(0, errtot), arb(0, errtot))
# Gram in beta basis
Gb = acb_mat(D, D)
for i in range(2 * N + 1): Gb[i, i] = 1
for idx, s in ((2 * N + 1, arb('0.5')), (2 * N + 2, arb('-0.5'))):
    for i, n in enumerate(band):
        v = ((s * L).exp() - 1) / ((acb(s, -om[n])) * sqL)      # <e_n, E_s>
        Gb[i, idx] = v; Gb[idx, i] = v.conjugate()
Gb[2 * N + 1, 2 * N + 1] = ((L).exp() - 1); Gb[2 * N + 2, 2 * N + 2] = (1 - (-L).exp())
Gb[2 * N + 1, 2 * N + 2] = Gb[2 * N + 2, 2 * N + 1] = acb(L)
# moment-zero basis Z (same pivots as fesh_arb_ab)
def mom(m, s):
    aa = acb(s, 2 * pi * m / L); return ((aa * L).exp() - 1) / aa
piv = [0, 1]; rest = [m for m in band if m not in piv]
Cp = acb_mat([[mom(m, s) for m in piv] for s in (arb('0.5'), arb('-0.5'))]).inv()
B = acb_mat(D, len(rest) + 2)
for j, m in enumerate(rest):
    B[band.index(m), j] = 1
    sol = Cp * acb_mat([[-mom(m, arb('0.5'))], [-mom(m, arb('-0.5'))]])
    for t_, p in enumerate(piv): B[band.index(p), j] = sol[t_, 0]
B[2 * N + 1, len(rest)] = 1; B[2 * N + 2, len(rest) + 1] = 1
Bh = B.conjugate().transpose()
G = Bh * Gb * B; M = Bh * M1 * B
trPiT = (G.inv() * M).trace().real
trT = L / pi * sum((sb * STEP for sb in SBAR), arb(0))
print("tr T =", trT); print("tr Pi T =", trPiT); print("tr P T P <=", (trT - trPiT).upper())
print("quadrature error per entry:", errtot)
json.dump({"trT": trT.str(30), "trPiT": trPiT.str(30), "trPTP_upper": str((trT - trPiT).upper())}, open("trace_arb.json", "w"))
