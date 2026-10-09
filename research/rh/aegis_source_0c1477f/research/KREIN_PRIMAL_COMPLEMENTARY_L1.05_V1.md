# Krein Primal Complementary Basis — L=1.05

**Status:** numerical diagnostic only · `RH_PROVEN=false` · `authority_effect=NONE`

## Experiment

Existing finite family: `(1/4-D^2)(sin(pi*x/L) sin(k*pi*x/L))`.

Complementary family:

`g1_k(x) = (k+2) sin(k*pi*x/L) - k sin((k+2)*pi*x/L)`, with `g_k=(1/4-D^2)g1_k`.

This satisfies `g1(0)=g1(L)=g1'(0)=g1'(L)=0` exactly. The committed family expands in cosine modes; this family expands in sine modes, so the tested finite trigonometric families are linearly independent.

## Direct comparison at T=3000, dt=0.02

| n | Existing basis | Complementary basis | Δ (new-old) | New / old | Strict Δ (T=6000, dt=0.01) |
|---:|---:|---:|---:|---:|---:|
| 32 | 0.0035075542174278 | 0.004216249891720253 | 7.087e-04 | 1.202048388 | 1.608e-08 |
| 64 | 0.00336326158912083 | 0.003842641996484291 | 4.794e-04 | 1.142534381 | 3.539e-08 |
| 96 | 0.003341292324069011 | 0.003696269897011346 | 3.550e-04 | 1.106239604 | 6.148e-08 |
| 128 | 0.003333792929111577 | 0.003616428300631429 | 2.826e-04 | 1.084778922 | 9.457e-08 |
| 160 | 0.003330945397030777 | 0.003569200783792885 | 2.383e-04 | 1.071527857 | 1.325e-07 |
| 192 | 0.003329504328650644 | 0.003534832427984024 | 2.053e-04 | 1.061669269 | 1.788e-07 |
| 224 | 0.003328783178465928 | 0.00351151439043924 | 1.827e-04 | 1.054894297 | 2.286e-07 |
| 256 | 0.003328400361988946 | 0.003492646017245106 | 1.642e-04 | 1.049346724 | 2.876e-07 |

## Numerical robustness

- Halving `dt` from `0.02` to `0.01` changes any checkpoint by at most `2.745e-15`.
- Extending `T` from `3000` to `6000` changes any checkpoint by at most `2.876e-07`; at `n=256` the shift is positive.
- At `n=256`, normalized Gram `cond₂ ≈ 6732.47`; raw scaling `cond₂ ≈ 2.07855e+13`.
- Generalized vs whitened eigenvalue difference: `3.300e-16`; normalized vs raw-scaling solve difference: `6.375e-16`.
- Small-n analytic-vs-Gauss self-check: Gram relative error `2.361e-14`, Fourier relative error `3.827e-13`.

## Interpretation

At `n=256`, the complementary family gives `0.003492646017245106` versus `0.003328400361988946` for the existing basis. The existing basis is therefore more adversarial at the matched checkpoint.

Simple tail fits on `n=128..256` extrapolate to `0.003369689879854558` (`a+b/n`) and `0.00335432583734019` (`a+b/n+c/n^2`). These are diagnostics only, not limit proofs.

**Falsification disposition:** `NO_NUMERICAL_FALSIFICATION_OBSERVED_IN_TESTED_REGIMES`. No tested value is nonpositive and the stricter numerical regimes do not create a surviving disagreement. However, the finite-dimensional sequence is still decreasing, so `zero_limit_inference=UNRESOLVED`.

Finite-subspace minima remain upper bounds on the unrestricted infimum. This result does **not** establish universal positivity and does **not** prove RH.

## Source binding

- Parent PR #699 head: `6399141cffaaca98d2dc96890810cd9a5551f455`
- Existing convergence script blob: `982bb18e3d8acdf88cde795d4fcd921d9581a972`
- Existing L=1.05 result blob: `24db597371010c6a5dc39f599c07c311e1c5bafc`
- Complementary script blob: `81c13703df9a48ef7e9387811c4c359e73dd8ab4`
