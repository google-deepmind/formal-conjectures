# Zeros on the critical line from sign changes (Turing, first half)

`RHCriticalLineSignV1` (Mathlib only, `[propext, Classical.choice, Quot.sound]`):

- `Xi_im`: `Λ(1/2 + it)` is real. The proof uses `completedRiemannZeta_one_sub`, `riemannZeta_conj`,
  `Gamma_conj` and `conj (1/2 + it) = 1 − (1/2 + it)`.
- `exists_zero_of_sign_change`: if `re Λ(1/2 + it)` changes sign on `[a, b]`, then `ζ(1/2 + t i) = 0`
  for some `t ∈ [a, b]`.

`RHRiemannThetaFormulaV1` (Mathlib only, standard axioms):

- `completedRiemannZeta_eq`: `Λ(s) = (𝓜A(s/2) + 𝓜A(1/2 − s/2))/2 − 1/s − 1/(1 − s)` with
  `A(x) = 1_{x>1}(θ(x) − 1)`, `θ(x) = Σ_{n∈ℤ} e^{−πn²x}` (Riemann's formula). On the line this is
  `Λ(1/2 + it) = ∫_1^∞ (θ(x) − 1) x^{−3/4} cos((t/2) log x) dx − 4/(1 + 4t²)`, with no Γ and no ζ;
  numerically it agrees with `π^{−s/2}Γ(s/2)ζ(s)` to 11 digits at t = 0, 5, 14, 14.3, 20.9, 21.1, 25, 25.1.

`RHLambdaLineV1` (imports the two above, standard axioms):

- `Xi_re_eq`: `re Λ(1/2 + it) = re 𝓜A(1/4 + it/2) − 1/(1/4 + t²)` (`A` is real, so the two Mellin
  terms are conjugate on the line).

`RHFixIntervalV1` (Mathlib only, standard axioms): fixed-point interval arithmetic, integers at
scale `2^{-p}` with outward rounding (`Iv.mem_add`, `Iv.mem_neg`, `Iv.mem_mul`), so the kernel can
evaluate enclosures with `decide`. `fixmirror.py` is the integer mirror of the full enclosure and the
spec for the Lean checker. It certifies `Λ(1/2+14i) < 0 < Λ(1/2+14.3i)`, `Λ(1/2+20.9i) > 0 > Λ(1/2+21.1i)`
and, with π to 80 digits, `Λ(1/2+24.9i) < 0`. At t ≈ 25 the 20-digit π of Mathlib is too coarse:
the cancellation amplifies its error about 10¹¹ times.

`RHThetaTailV1` (Mathlib only, standard axioms): `θ(t) − 1 = Σ_{n≥1} 2e^{−πn²t}` and, for `t ≥ 1`,
`0 ≤ θ(t) − 1 − Σ_{n=1}^{3} 2e^{−πn²t} ≤ 4e^{−16πt}` (`theta_tail_bound`).

Next: `𝓜A(w) = 2 Σ_{n≤3} ∫_1^X e^{−πn²x} x^{w−1} dx` plus explicit tails, a per-cell Taylor model of
`x^{w−1}` (44 cells of width 1/4, degree 12: remainder ≤ 5·10⁻¹¹ against |Λ(1/2 + 14i)| ≈ 2·10⁻⁶), and a
rational checker run by the kernel at t = 14 and t = 14.3.

Still open for "every zero with `0 < γ < T` lies on the line":

1. rigorous enclosures of `Λ(1/2 + it)` at sample points (ζ and Γ in interval arithmetic);
2. the zero count `N(T)` (argument principle plus the Backlund/Turing bound on `S(t)`).

This is verification up to a height, not RH. AUTHORITY_EFFECT = NONE.
