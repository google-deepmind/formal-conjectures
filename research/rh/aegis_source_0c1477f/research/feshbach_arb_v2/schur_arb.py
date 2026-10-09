"""Rigorous Schur step: S = A11 - mu G11 - C_B/(c_inf - mu) > 0 (Hermitian).
S = R + iJ with J antisymmetric; v*Sv >= v*(R - ||J|| I)v, ||J|| <= k max|J_ij|.  Interval Cholesky of R - ||J|| I."""
import sys, json
from flint import arb, acb, ctx
ctx.prec = 320
P = json.load(open(sys.argv[1])); cinf = arb(sys.argv[2])
def M(name): return [[acb(arb(re), arb(im)) for re, im in row] for row in P[name]]
A, G, C = M('A11'), M('G11'), M('CB'); k = len(A)
def pd(mu):
    S = [[A[i][j] - mu * G[i][j] - C[i][j] / (cinf - mu) for j in range(k)] for i in range(k)]
    jn = k * max(abs(S[i][j].imag).upper() for i in range(k) for j in range(k))
    X = [[S[i][j].real - (jn if i == j else 0) for j in range(k)] for i in range(k)]
    Lm = [[arb(0)] * k for _ in range(k)]; minpiv = None
    for j in range(k):
        d = X[j][j] - sum((Lm[j][t] ** 2 for t in range(j)), arb(0))
        if not d > 0: return False, j, d, jn
        minpiv = d if minpiv is None or d < minpiv else minpiv
        Lm[j][j] = d.sqrt()
        for i in range(j + 1, k):
            Lm[i][j] = (X[i][j] - sum((Lm[i][t] * Lm[j][t] for t in range(j)), arb(0))) / Lm[j][j]
    return True, None, minpiv, jn
for mu in sys.argv[3:]:
    ok, j, d, jn = pd(arb(mu))
    print(f"mu={mu}: " + (f"POSITIVE DEFINITE, min Cholesky pivot {d}" if ok else f"FAILED at pivot {j}: {d}") + f"  (||J|| <= {jn})")
