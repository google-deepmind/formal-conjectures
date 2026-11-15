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
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Stationary Gaussian autoregressions

A parameter has real coefficients of order at most `p` and positive innovation variance.
`IsGaussianARLaw` specifies a law on integer-indexed real paths. It requires a centered,
stationary Gaussian process whose autoregressive residuals are independent Gaussian variables.
No existence or uniqueness theorem for stationary solutions is needed to define this predicate.

The normalization is $\phi(z)=1-\sum_{j=1}^p\phi_jz^j$.

*Reference:* M. Mlikota, [Parameter Identification and Inference in Discretely Sampled or
Temporally Aggregated Autoregressions](https://arxiv.org/abs/2608.13224v2), §1, equation (1).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TimeSeries.Autoregression

/-- Integer-indexed real paths, with the product measurable space. -/
abbrev Path := ℤ → ℝ

/-- Real autoregressive coefficients of order at most `p`, with positive innovation variance. -/
structure Parameter (p : ℕ) where
  coefficient : Fin p → ℝ
  innovationVariance : ℝ≥0
  variance_pos : 0 < innovationVariance

/-- The polynomial $1-\sum_{j=1}^p\phi_jz^j$, viewed over the complex numbers. -/
def Parameter.polynomial {p : ℕ} (θ : Parameter p) : Polynomial ℂ :=
  1 - ∑ j : Fin p, Polynomial.C (θ.coefficient j : ℂ) * Polynomial.X ^ (j.val + 1)

/-- Stationary autoregressive parameters have no polynomial zero in the closed unit disk. -/
def Parameter.IsStationary {p : ℕ} (θ : Parameter p) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → θ.polynomial.eval z ≠ 0

/-- Exact order `p`: the coefficient at lag `p` is nonzero. -/
def Parameter.HasExactOrder {p : ℕ} (θ : Parameter p) : Prop :=
  ∃ j : Fin p, j.val + 1 = p ∧ θ.coefficient j ≠ 0

/-- Translating an integer-indexed path. -/
def shift (s : ℤ) (x : Path) : Path := fun t ↦ x (t + s)

@[fun_prop]
lemma measurable_shift (s : ℤ) : Measurable (shift s) := by
  fun_prop [shift]

/-- The innovation at time `t`, obtained as the autoregressive residual. -/
def innovation {p : ℕ} (θ : Parameter p) (t : ℤ) (x : Path) : ℝ :=
  x t - ∑ j : Fin p, θ.coefficient j * x (t - (j.val + 1 : ℕ))

@[fun_prop]
lemma measurable_innovation {p : ℕ} (θ : Parameter p) (t : ℤ) :
    Measurable (innovation θ t) := by
  fun_prop [innovation]

/-- A centered stationary Gaussian AR law with independent $N(0,v)$ innovations.

The autoregressive equation holds pointwise because `innovation` is the residual map.
Stationarity is equality of the full path law under every integer translation.
-/
structure IsGaussianARLaw {p : ℕ} (θ : Parameter p) (μ : Measure Path) : Prop where
  probability : IsProbabilityMeasure μ
  stationary : ∀ s : ℤ, μ.map (shift s) = μ
  gaussian : IsGaussianProcess (fun t (x : Path) ↦ x t) μ
  centered : ∀ t : ℤ, ∫ x, x t ∂μ = 0
  independent_innovations : iIndepFun (innovation θ) μ
  innovation_law : ∀ t : ℤ, μ.map (innovation θ t) = gaussianReal 0 θ.innovationVariance

/-- Every coordinate of a Gaussian autoregressive path is integrable. -/
lemma IsGaussianARLaw.integrable {p : ℕ} {θ : Parameter p} {μ : Measure Path}
    (h : IsGaussianARLaw θ μ) (t : ℤ) : Integrable (fun x ↦ x t) μ :=
  (h.gaussian.hasGaussianLaw_eval t).integrable

/-- Changing all odd-lag coefficient signs, with the same innovation variance. -/
def Parameter.signFlip {p : ℕ} (θ : Parameter p) : Parameter p where
  coefficient j := (-1) ^ (j.val + 1) * θ.coefficient j
  innovationVariance := θ.innovationVariance
  variance_pos := θ.variance_pos

@[simp]
lemma Parameter.signFlip_variance {p : ℕ} (θ : Parameter p) :
    θ.signFlip.innovationVariance = θ.innovationVariance := rfl

@[simp]
lemma Parameter.signFlip_signFlip {p : ℕ} (θ : Parameter p) :
    θ.signFlip.signFlip = θ := by
  cases θ with
  | mk c v hv =>
    simp only [signFlip]
    congr 1
    funext j
    rw [← mul_assoc, ← mul_pow]
    simp

/-- Alternating the coefficient signs evaluates the original polynomial at the negated input. -/
lemma Parameter.eval_polynomial_signFlip {p : ℕ} (θ : Parameter p) (z : ℂ) :
    θ.signFlip.polynomial.eval z = θ.polynomial.eval (-z) := by
  simp only [polynomial, signFlip, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← neg_one_mul z, mul_pow]
  ring

/-- The alternating coefficient transform preserves the stationary parameter domain. -/
lemma Parameter.IsStationary.signFlip {p : ℕ} {θ : Parameter p} (hθ : θ.IsStationary) :
    θ.signFlip.IsStationary := by
  intro z hz
  rw [Parameter.eval_polynomial_signFlip]
  exact hθ (-z) (by simpa using hz)

/-- An order-at-most-one parameter with coefficient `a`. -/
def firstOrder (a : ℝ) (v : ℝ≥0) (hv : 0 < v) : Parameter 1 where
  coefficient _ := a
  innovationVariance := v
  variance_pos := hv

@[simp]
lemma firstOrder_polynomial (a : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    (firstOrder a v hv).polynomial = 1 - Polynomial.C (a : ℂ) * Polynomial.X := by
  simp [Parameter.polynomial, firstOrder]

lemma firstOrder_isStationary {a : ℝ} (ha : |a| < 1) (v : ℝ≥0) (hv : 0 < v) :
    (firstOrder a v hv).IsStationary := by
  intro z hz
  simp only [firstOrder_polynomial, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hprod : ‖(a : ℂ) * z‖ < 1 := by
    calc
      ‖(a : ℂ) * z‖ = ‖(a : ℂ)‖ * ‖z‖ := norm_mul _ _
      _ ≤ ‖(a : ℂ)‖ := by nlinarith [norm_nonneg (a : ℂ)]
      _ < 1 := by simpa using ha
  intro h
  have heq : ‖(a : ℂ) * z‖ = 1 := by rw [← sub_eq_zero.mp h]; simp
  linarith

lemma firstOrder_hasExactOrder {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0) (hv : 0 < v) :
    (firstOrder a v hv).HasExactOrder :=
  ⟨0, rfl, ha⟩

/-- A nonzero lag-one coefficient distinguishes a parameter from its sign transform. -/
lemma firstOrder_signFlip_ne {a : ℝ} (ha : a ≠ 0) (v : ℝ≥0) (hv : 0 < v) :
    (firstOrder a v hv).signFlip ≠ firstOrder a v hv := by
  intro h
  have hcoeff := congrArg (fun θ : Parameter 1 ↦ θ.coefficient 0) h
  simp [Parameter.signFlip, firstOrder] at hcoeff
  exact ha (by linarith)

/-- A white-noise parameter is permitted even when the coefficient vector has positive length. -/
def whiteNoise (p : ℕ) (v : ℝ≥0) (hv : 0 < v) : Parameter p where
  coefficient _ := 0
  innovationVariance := v
  variance_pos := hv

@[simp]
lemma whiteNoise_polynomial (p : ℕ) (v : ℝ≥0) (hv : 0 < v) :
    (whiteNoise p v hv).polynomial = 1 := by
  simp [Parameter.polynomial, whiteNoise]

lemma whiteNoise_isStationary (p : ℕ) (v : ℝ≥0) (hv : 0 < v) :
    (whiteNoise p v hv).IsStationary := by
  intro z _
  simp

@[simp]
lemma innovation_whiteNoise (p : ℕ) (v : ℝ≥0) (hv : 0 < v) (t : ℤ) :
    innovation (whiteNoise p v hv) t = fun x ↦ x t := by
  funext x
  simp [innovation, whiteNoise]

/-- The law of an integer-indexed sequence of independent centered Gaussian variables. -/
def whiteNoiseLaw (v : ℝ≥0) : Measure Path :=
  Measure.infinitePi (fun _ : ℤ ↦ gaussianReal 0 v)

lemma whiteNoiseLaw_eval (v : ℝ≥0) (t : ℤ) :
    (whiteNoiseLaw v).map (fun x ↦ x t) = gaussianReal 0 v :=
  Measure.infinitePi_map_eval _ _

/-- The Gaussian AR law predicate is inhabited, including lower-order competing models. -/
lemma isGaussianARLaw_whiteNoise (p : ℕ) (v : ℝ≥0) (hv : 0 < v) :
    IsGaussianARLaw (whiteNoise p v hv) (whiteNoiseLaw v) where
  probability := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))
  stationary s := by
    exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h ↦ add_right_cancel h)
  gaussian := by
    constructor
    intro I
    have h := iIndepFun_infinitePi (P := fun _ : ℤ ↦ gaussianReal 0 v)
      (X := fun _ x ↦ x) (by fun_prop)
    apply iIndepFun.hasGaussianLaw
    · intro i
      exact HasLaw.hasGaussianLaw ⟨by fun_prop, whiteNoiseLaw_eval v i⟩
    · exact h.precomp Subtype.val_injective
  centered t := by
    change ∫ x, id (x t) ∂whiteNoiseLaw v = 0
    rw [← integral_map (measurable_pi_apply t).aemeasurable
      (by fun_prop : AEStronglyMeasurable id ((whiteNoiseLaw v).map (fun x ↦ x t)))]
    rw [whiteNoiseLaw_eval]
    exact integral_id_gaussianReal
  independent_innovations := by
    have h : innovation (whiteNoise p v hv) = fun t x ↦ x t :=
      funext (innovation_whiteNoise p v hv)
    rw [h]
    exact iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  innovation_law t := by
    rw [innovation_whiteNoise]
    exact whiteNoiseLaw_eval v t

/-- Innovation variance changes produce different white-noise path laws. -/
lemma whiteNoiseLaw_injective : Function.Injective whiteNoiseLaw := by
  intro v w h
  have h0 := congrArg (fun μ : Measure Path ↦ μ.map (fun x ↦ x 0)) h
  simpa only [whiteNoiseLaw_eval, gaussianReal_ext_iff, true_and] using h0

end TimeSeries.Autoregression
