/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil

/-! # Equivalents to the Riemann Hypothesis

This file contains formal statements that are known to be equivalent to the Riemann Hypothesis,
following the survey [Co26], §4.

*References:*
* [Co26] A. Connes, [The Riemann Hypothesis: Past, Present and a Letter Through
  Time](https://arxiv.org/abs/2602.04022), 2026.
-/

open Real MeasureTheory
open scoped ArithmeticFunction.sigma CompactlySupported Convolution ContDiff

namespace RiemannHypothesis

/-- **Robin's Criterion**. The Riemann Hypothesis is equivalent to
$$
  \sigma(n) < e ^ {\gamma} n\log\log n
$$
for all $n > 5040$, where $\gamma$ is the Euler-Mascheroni constant and $\sigma(n)$ is
the sum of divisors.
-/
@[category research solved, AMS 11]
theorem robin_criterion :
    RiemannHypothesis ↔ ∀ n > 5040, σ 1 n < (exp eulerMascheroniConstant) * n * log (log n) := by
  sorry

/-- The statement that Robin's criterion holds. -/
@[category research open, AMS 11]
theorem robin_criterion_rhs {n : ℕ} (hn : n > 5040) :
    σ 1 n < exp eulerMascheroniConstant * n * log (log n) := by
  sorry

/-- **Lagarias' Criterion**. A refinement of Robin's criterion: the Riemann Hypothesis
is equivalent to
$$
  \sigma(n) < H_n + e^{H_n}\log H_n
$$
for all $n \geq 2$, where $H_n = 1 + 1/2 + \cdots + 1/n$ is the $n$th harmonic number.

Note that [Co26] states this for all $n \geq 1$, but at $n = 1$ both sides equal $1$; Lagarias'
original formulation is the non-strict inequality for all $n \geq 1$, with equality only at
$n = 1$. -/
@[category research solved, AMS 11]
theorem lagarias_criterion : RiemannHypothesis ↔
    ∀ n > 1, σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n) := by
  sorry

/-- The statement that Lagarias' criterion holds. -/
@[category research open, AMS 11]
theorem lagarias_criterion_rhs {n : ℕ} (hn : 1 < n) :
    σ 1 n < harmonic n + exp (harmonic n) * log (harmonic n) := by
  sorry

/-- The nontrivial zeros of the Riemann zeta function with positive imaginary part. Since the
nontrivial zeros are closed under complex conjugation, these determine all nontrivial zeros. -/
def nontrivialPosZeros : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ riemannZeta z = 0}

/-- The numbers
$$
  \lambda_n := \sum_{\rho}\left(1 - \left(1 - \frac{1}{\rho}\right)^n\right)
$$
appearing in Li's criterion, summing over the nontrivial zeros $\rho$ of the
Riemann zeta function.

This is a real number because nontrivial zeros always come in conjugate pairs.
Note that, as stated, the sum is only conditionally convergent, however it is absolutely convergent
when taken in conjugate pairs, since $1/\rho + 1/\bar\rho = 2\Re\rho/|\rho|^2$. Hence we sum
over the zeros with positive imaginary part with summand `2 * (_).re`, which makes the unordered
sum `∑'` meaningful. -/
noncomputable def lambda (n : ℕ) : ℝ := ∑' ρ : nontrivialPosZeros, 2 * (1 - (1 - 1 / ρ.1) ^ n).re

/-- **Li's Criterion**. The Riemann Hypothesis is equivalent to the positivity of
$$
  \lambda_n := \sum_{\rho}\left(1 - \left(1 - \frac{1}{\rho}\right)^n\right)
$$
for each $n > 0$.
-/
@[category research solved, AMS 11]
theorem li_criterion : RiemannHypothesis ↔ ∀ n > 0, 0 < lambda n := by
  sorry

/-- The statement that Li's criterion holds. -/
@[category research open, AMS 11]
theorem li_criterion_rhs {n : ℕ} (hn : 0 < n) : 0 < lambda n := by sorry

/-- The function $\rho_{\theta} := \left\{\frac{\theta}{x}\right\}$ appearing in the
Beurling-Nyman criterion. -/
noncomputable def fractScalarInv (θ : ℝ) (x : ℝ) : ℝ := Int.fract (θ / x)

@[category API, AMS 11 28]
theorem aEStronglyMeasurable_fractScalarInv (θ : ℝ) : AEStronglyMeasurable (fractScalarInv θ) :=
  (measurable_fract.comp (measurable_const.div measurable_id)).aestronglyMeasurable

@[category API, AMS 11 28]
theorem fractScalarInv_memLp2 (θ : ℝ) :
    MemLp (fractScalarInv θ) 2 (volume.restrict (Set.Ioc 0 1)) :=
  .of_bound (aEStronglyMeasurable_fractScalarInv θ).restrict 1 <|
    Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le

/-- The linear combination $\sum_{\nu = 1}^n c_{\nu}\rho_{\theta_\nu}$ expressed explicitly as an
element of $L^2(0, 1)$. -/
noncomputable def fractScalarInvSumL2 (n : ℕ) (c θ : Fin n → ℝ) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ∑ ν, c ν • (fractScalarInv_memLp2 (θ ν)).toLp _

/-- **Beurling-Nyman Criterion**. The Riemann Hypothesis is equivalent to the statement that
the set of finite linear combination $\sum_{\nu = 1}^n c_{\nu}\rho_{\theta_{\nu}}$ is dense
in $L^2(0, 1)$, when ranging over $0 < \theta_{\nu}\leq 1$ and
$\sum_{\nu = 1}^n c_{\nu}\theta_{\nu} = 0$. -/
@[category research solved, AMS 11 28]
theorem beurling_nyman_criterion : RiemannHypothesis ↔
    Dense { fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0)} := by
  sorry

/-- The statement that the Beurling-Nyman criterion holds. -/
@[category research open, AMS 11 28]
theorem beurling_nyman_criterion_rhs :
    Dense { fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0)} := by
  sorry

/-- The additive Archimedean factor appearing in the Weil criterion. -/
noncomputable def weilArchimedean (f : ℝ → ℝ) : ℝ :=
  ((4 * π).log + eulerMascheroniConstant) * f 0 +
    ∫ x in Set.Ioi 0, (f x + f (-x) - 2 * exp (-x / 2) * f 0) * exp (x / 2) / (exp x - exp (-x))

/-- The additive non-Archimedean factor appearing in the Weil criterion. -/
noncomputable def weilNonArchimedean (p : ℕ) (f : ℝ → ℝ) : ℝ :=
    log p * ∑' m : ℕ, exp (-(m + 1) * log p / 2) * (f ((m + 1) * log p) + f (-(m + 1) * log p))

/-- The additive condition on test functions. The property in [Co26] that $\hat{g}(\pm i/2) = 0$,
where $\hat{g}$ is the Mellin transform, corresponds to the vanishing of the Fourier transform
at $\pm 1/2$. -/
def IsTestFunction (g : ℝ → ℝ) : Prop := ∫ x, g x * exp (x / 2) = 0 ∧ ∫ x, g x * exp (-x / 2) = 0

/-- **Weil's Positivity Criterion**. The Riemann Hypothesis is equivalent to the non-positivity of
Weil factor sums on the convolution of test functions. In [Co26] this is expressed as
$$
  \sum_v W_v(g\star g^*) \leq 0
$$
for all compactly-supported smooth functions $g : \mathbb{R}_+^{\times} \to \mathbb{C}$ such that
the Mellin transform of $g$ vanishes at $\pm i / 2$, where $g^*(x) := \bar{g}(x^{-1})$ and $W_v$
are the multiplicative Weil factors defined in [Co26]. We formalise this as the corresponding
additive statement (via $x = e^u$), since convolution in mathlib is additive, and restrict to
real-valued test functions $g$, which suffices for the equivalence. -/
@[category research solved, AMS 11 46]
theorem weil_positivity_criterion :
    RiemannHypothesis ↔ ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0 := by
  sorry

/-- The statement that the Weil criterion holds. -/
@[category research open, AMS 11 46]
theorem weil_positivity_criterion_rhs {g : C_c(ℝ, ℝ)} (hg : ContDiff ℝ ∞ g)
    (h : IsTestFunction g) :
    weilArchimedean (g ⋆ fun x ↦ g (-x)) +
      ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0 := by
  sorry

end RiemannHypothesis
