/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesTest.PeriodIntegral.RealRoots
import FormalConjecturesTest.RealComponents
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure

/-!
# The real period of an elliptic curve as an integral

Let $E$ be an elliptic curve over $\mathbb{R}$ with Weierstrass equation
$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ and invariant differential
$\omega = \frac{dx}{2y + a_1 x + a_3}$. Completing the square,
$(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6 =: F(x)$, the *two-torsion cubic*
`WeierstrassCurve.twoTorsionPolynomial`. The identity component of $E(\mathbb{R})$ consists of the
point at infinity and the real points with $x \geq e_1$, where $e_1$ is the largest real root of
$F$; over $x > e_1$ it has the two branches $2y + a_1 x + a_3 = \pm\sqrt{F(x)}$, on each of which
$|\omega| = \frac{dx}{\sqrt{F(x)}}$. Hence
$$\int_{E(\mathbb{R})^0} |\omega| = 2 \int_{e_1}^{\infty} \frac{dx}{\sqrt{4x^3 + b_2 x^2 + 2 b_4 x
+ b_6}},$$
which is the classical formula $2\omega_1 = \int_{e_1}^\infty \frac{du}{\sqrt{(u - e_1)(u - e_2)
(u - e_3)}}$ for the real period of a real lattice.

This file defines
* `WeierstrassCurve.e₁`, the largest real root of the two-torsion cubic of a Weierstrass curve over
  $\mathbb{R}$;
* `WeierstrassCurve.realPeriodIntegrand`, the density $x \mapsto 1 / \sqrt{F(x)}$;
* `WeierstrassCurve.leastRealPeriodIntegral`, the integral $2 \int_{e_1}^\infty dx / \sqrt{F(x)}$
  over the identity component;
* `WeierstrassCurve.realPeriodIntegral`, the **real period** of the Birch and Swinnerton-Dyer
  conjecture: the previous integral multiplied by the number of connected components of
  $E(\mathbb{R})$, `WeierstrassCurve.nrRealComponents`, which is $2$ or $1$ according as the
  discriminant is positive or negative;

and proves that for an elliptic curve the integrand is integrable
(`WeierstrassCurve.integrableOn_realPeriodIntegrand`), so that both periods are positive
(`WeierstrassCurve.leastRealPeriodIntegral_pos`, `WeierstrassCurve.realPeriodIntegral_pos`). The
substitution $x = X - b_2 / 12$ turns $F$ into the depressed cubic $4X^3 - g_2 X - g_3$ with
$g_2 = c_4 / 12$ and $g_3 = c_6 / 216$
(`WeierstrassCurve.leastRealPeriodIntegral_eq_integral_depressed`). These are the invariants of the
period lattice `WeierstrassCurve.periodPair` of `FormalConjecturesTest.RealPeriod`, whose least
positive real element is the lattice-theoretic `WeierstrassCurve.leastRealPeriod`, with real period
`WeierstrassCurve.realPeriod`. That the two versions agree is proved in
`FormalConjecturesTest.RealPeriodIntegral`.

When $\Delta > 0$ the bounded component of $E(\mathbb{R})$ contributes the same amount as the
identity component (the second equality in DLMF 23.6.34), so the real period is also
$2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$ with the integrand taken to be $0$ where $F \leq 0$. That
reformulation is not proved here either.

*References:*
- [LMFDB](https://beta.lmfdb.org/knowledge/show/ec.period), knowls `ec.period`,
  `ec.q.real_period` and `ec.q.period_lattice`
- [DLMF](https://dlmf.nist.gov/23.6.iv), §23.5 and §23.6(iv), equations 23.6.34 and 23.6.36
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
-/

open MeasureTheory Polynomial Set Filter

noncomputable section

namespace MeasureTheory

/-- Translating a set integral over a half-line:
$\int_a^\infty g(x + c) \, dx = \int_{a + c}^\infty g(x) \, dx$. -/
theorem integral_comp_add_right_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (a c : ℝ) : ∫ x in Ioi a, g (x + c) = ∫ x in Ioi (a + c), g x := by
  simpa using (measurePreserving_add_right volume c).setIntegral_preimage_emb
    (measurableEmbedding_addRight c) g (Ioi (a + c))

end MeasureTheory

namespace WeierstrassCurve

/- ## The two-torsion cubic -/

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The two-torsion cubic is $4x^3 + b_2 x^2 + 2 b_4 x + b_6$. -/
lemma eval_toPoly_twoTorsionPolynomial (x : R) :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPolynomial, Cubic.toPoly]

variable [NeZero (4 : R)]

lemma toPoly_twoTorsionPolynomial_ne_zero : W.twoTorsionPolynomial.toPoly ≠ 0 :=
  Cubic.ne_zero_of_a_ne_zero four_ne_zero

@[simp]
lemma natDegree_toPoly_twoTorsionPolynomial : W.twoTorsionPolynomial.toPoly.natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero four_ne_zero

@[simp]
lemma leadingCoeff_toPoly_twoTorsionPolynomial : W.twoTorsionPolynomial.toPoly.leadingCoeff = 4 :=
  Cubic.leadingCoeff_of_a_ne_zero four_ne_zero

end CommRing

variable (W : WeierstrassCurve ℝ)

/- ## The largest real root -/

/-- The largest real root $e_1$ of the two-torsion cubic $4x^3 + b_2 x^2 + 2 b_4 x + b_6$. A real
cubic has a real root, so this is a root, and the greatest one. If the discriminant is positive all
three roots $e_1 > e_2 > e_3$ are real; if it is negative, $e_1$ is the only real root. -/
def e₁ : ℝ := sSup {x : ℝ | W.twoTorsionPolynomial.toPoly.IsRoot x}

lemma finite_setOf_isRoot_twoTorsionPolynomial :
    {x : ℝ | W.twoTorsionPolynomial.toPoly.IsRoot x}.Finite :=
  finite_setOfPred_isRoot W.toPoly_twoTorsionPolynomial_ne_zero

lemma isRoot_e₁ : W.twoTorsionPolynomial.toPoly.IsRoot W.e₁ :=
  Set.Nonempty.csSup_mem
    (exists_isRoot_of_odd_natDegree (by rw [W.natDegree_toPoly_twoTorsionPolynomial]; decide))
    W.finite_setOf_isRoot_twoTorsionPolynomial

lemma le_e₁_of_isRoot {x : ℝ} (hx : W.twoTorsionPolynomial.toPoly.IsRoot x) : x ≤ W.e₁ :=
  le_csSup W.finite_setOf_isRoot_twoTorsionPolynomial.bddAbove hx

/-- A root with no root to its right is $e_1$. -/
lemma e₁_eq_of_isRoot {e : ℝ} (he : W.twoTorsionPolynomial.toPoly.IsRoot e)
    (h : ∀ x, e < x → ¬ W.twoTorsionPolynomial.toPoly.IsRoot x) : W.e₁ = e :=
  le_antisymm (not_lt.mp fun hlt ↦ h _ hlt W.isRoot_e₁) (W.le_e₁_of_isRoot he)

/-- The two-torsion cubic is positive to the right of $e_1$. -/
lemma eval_toPoly_twoTorsionPolynomial_pos {x : ℝ} (hx : W.e₁ < x) :
    0 < W.twoTorsionPolynomial.toPoly.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun r hr ↦ (W.le_e₁_of_isRoot hr).trans_lt hx)
    (by rw [W.leadingCoeff_toPoly_twoTorsionPolynomial]; norm_num)

/-- For an elliptic curve $e_1$ is a simple root of the two-torsion cubic, whose discriminant is
$16 \Delta \neq 0$. -/
lemma rootMultiplicity_e₁ [W.IsElliptic] :
    rootMultiplicity W.e₁ W.twoTorsionPolynomial.toPoly = 1 :=
  le_antisymm
    (Cubic.rootMultiplicity_le_one_of_discr_ne_zero four_ne_zero
      (W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr two_ne_zero)) _)
    ((rootMultiplicity_pos W.toPoly_twoTorsionPolynomial_ne_zero).mpr W.isRoot_e₁)

/-- The two-torsion cubic of an elliptic curve factors as $(x - e_1) Q(x)$ with $Q$ positive on
$[e_1, \infty)$. -/
lemma exists_toPoly_twoTorsionPolynomial_eq_X_sub_C_mul [W.IsElliptic] : ∃ Q : ℝ[X],
    W.twoTorsionPolynomial.toPoly = (X - C W.e₁) * Q ∧ ∀ x, W.e₁ ≤ x → 0 < Q.eval x := by
  obtain ⟨Q, hQ, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    W.twoTorsionPolynomial.toPoly W.toPoly_twoTorsionPolynomial_ne_zero W.e₁
  rw [W.rootMultiplicity_e₁, pow_one] at hQ
  refine ⟨Q, hQ, fun x hx ↦ zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun r hr ↦ ?_) ?_⟩
  · have hrF : W.twoTorsionPolynomial.toPoly.IsRoot r := by
      rw [IsRoot, hQ, eval_mul, hr.eq_zero, mul_zero]
    exact ((W.le_e₁_of_isRoot hrF).lt_of_ne fun h ↦ hdvd (dvd_iff_isRoot.mpr (h ▸ hr))).trans_le hx
  · rw [← leadingCoeff_monic_mul (monic_X_sub_C W.e₁), ← hQ,
      W.leadingCoeff_toPoly_twoTorsionPolynomial]
    norm_num

/- ## The integrand -/

/-- The density $|\omega| / dx = 1 / \sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}$ of the invariant
differential on either branch of the real locus, as a function on $\mathbb{R}$, with the junk value
$0$ where the cubic is not positive. -/
def realPeriodIntegrand (x : ℝ) : ℝ := (√(W.twoTorsionPolynomial.toPoly.eval x))⁻¹

lemma realPeriodIntegrand_nonneg (x : ℝ) : 0 ≤ W.realPeriodIntegrand x :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma realPeriodIntegrand_pos {x : ℝ} (hx : W.e₁ < x) : 0 < W.realPeriodIntegrand x :=
  inv_pos.mpr (Real.sqrt_pos.mpr (W.eval_toPoly_twoTorsionPolynomial_pos hx))

lemma measurable_realPeriodIntegrand : Measurable W.realPeriodIntegrand :=
  (Real.continuous_sqrt.comp W.twoTorsionPolynomial.toPoly.continuous).measurable.inv

/-- Eventually $x^3 \leq 4x^3 + b_2 x^2 + 2 b_4 x + b_6$. -/
lemma eventually_pow_three_le_eval_toPoly_twoTorsionPolynomial :
    ∀ᶠ x in atTop, x ^ 3 ≤ W.twoTorsionPolynomial.toPoly.eval x := by
  have h := W.twoTorsionPolynomial.toPoly.isEquivalent_atTop_lead.isLittleO.def
    (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [W.natDegree_toPoly_twoTorsionPolynomial,
    W.leadingCoeff_toPoly_twoTorsionPolynomial, Pi.sub_apply, Real.norm_eq_abs] at h
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * x ^ 3)] at hx
  linarith [(abs_le.mp hx).1, pow_nonneg hx0 3]

/-- Integrability at infinity: the integrand is integrable on $(c, \infty)$ as soon as
$x^3 \leq F(x)$ holds there. -/
lemma integrableOn_realPeriodIntegrand_Ioi {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c ≤ x → x ^ 3 ≤ W.twoTorsionPolynomial.toPoly.eval x) :
    IntegrableOn W.realPeriodIntegrand (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hc).mono'
    W.measurable_realPeriodIntegrand.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hc.trans hx
  rw [Real.norm_eq_abs, abs_of_nonneg (W.realPeriodIntegrand_nonneg x),
    show x ^ (-3 / 2 : ℝ) = (√(x ^ 3))⁻¹ by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le,
        ← Real.rpow_neg hx0.le]
      norm_num]
  exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt (h x hx.le))

/-- Integrability at the simple root $e_1$: there $F(x) = (x - e_1) Q(x)$ with $Q$ positive, so the
integrand is $(x - e_1)^{-1/2}$ times a continuous function. -/
lemma integrableOn_realPeriodIntegrand_Ioc [W.IsElliptic] {c : ℝ} (hc : W.e₁ ≤ c) :
    IntegrableOn W.realPeriodIntegrand (Ioc W.e₁ c) := by
  obtain ⟨Q, hQ, hQpos⟩ := W.exists_toPoly_twoTorsionPolynomial_eq_X_sub_C_mul
  have hr : IntegrableOn (fun x : ℝ ↦ (x - W.e₁) ^ (-(1 / 2) : ℝ)) (Icc W.e₁ c) := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp ?_
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c - W.e₁)
        (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_right W.e₁
  have hg : ContinuousOn (fun x : ℝ ↦ (√(Q.eval x))⁻¹) (Icc W.e₁ c) :=
    (Real.continuous_sqrt.comp Q.continuous).continuousOn.inv₀ fun x hx ↦
      (Real.sqrt_pos.mpr (hQpos x hx.1)).ne'
  refine ((hr.mul_continuousOn hg isCompact_Icc).mono_set Ioc_subset_Icc_self).congr_fun
    (fun x hx ↦ ?_) measurableSet_Ioc
  have hx1 : (0 : ℝ) ≤ x - W.e₁ := sub_nonneg.mpr hx.1.le
  change (x - W.e₁) ^ (-(1 / 2) : ℝ) * (√(Q.eval x))⁻¹ = _
  rw [realPeriodIntegrand, hQ, eval_mul, eval_sub, eval_X, eval_C, Real.sqrt_mul hx1, mul_inv,
    Real.rpow_neg hx1, ← Real.sqrt_eq_rpow]

/-- The integrand is integrable on $(e_1, \infty)$. -/
lemma integrableOn_realPeriodIntegrand [W.IsElliptic] :
    IntegrableOn W.realPeriodIntegrand (Ioi W.e₁) := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp W.eventually_pow_three_le_eval_toPoly_twoTorsionPolynomial
  have hec : W.e₁ ≤ max R₀ (max W.e₁ 1) := le_max_of_le_right (le_max_left _ _)
  rw [← Ioc_union_Ioi_eq_Ioi hec]
  exact (W.integrableOn_realPeriodIntegrand_Ioc hec).union
    (W.integrableOn_realPeriodIntegrand_Ioi
      (zero_lt_one.trans_le (le_max_of_le_right (le_max_right _ _)))
      fun x hx ↦ hR₀ x ((le_max_left _ _).trans hx))

/- ## The least positive real period as an integral -/

/-- The least positive real period as an integral,
$2 \int_{e_1}^\infty \frac{dx}{\sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}}$: the integral of $|\omega|$
over the identity component of $E(\mathbb{R})$. -/
def leastRealPeriodIntegral : ℝ := 2 * ∫ x in Ioi W.e₁, W.realPeriodIntegrand x

/-- The least positive real period of an elliptic curve over $\mathbb{R}$ is positive. -/
lemma leastRealPeriodIntegral_pos [W.IsElliptic] : 0 < W.leastRealPeriodIntegral := by
  refine mul_pos two_pos ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall W.realPeriodIntegrand_nonneg) W.integrableOn_realPeriodIntegrand,
    show Function.support W.realPeriodIntegrand ∩ Ioi W.e₁ = Ioi W.e₁ from
      inter_eq_right.mpr fun x hx ↦ (W.realPeriodIntegrand_pos hx).ne', Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- The substitution $x = X - b_2 / 12$ turns the two-torsion cubic into the depressed cubic
$4X^3 - g_2 X - g_3$ with $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$. -/
lemma eval_toPoly_twoTorsionPolynomial_sub (x : ℝ) :
    W.twoTorsionPolynomial.toPoly.eval (x - W.b₂ / 12) =
      4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216 := by
  simp only [eval_toPoly_twoTorsionPolynomial, c₄, c₆, b₄]
  ring

/-- The real period integral in terms of the depressed cubic $4X^3 - g_2 X - g_3$ with
$g_2 = c_4 / 12$ and $g_3 = c_6 / 216$, the invariants of the period lattice of the curve. -/
lemma leastRealPeriodIntegral_eq_integral_depressed : W.leastRealPeriodIntegral =
    2 * ∫ x in Ioi (W.e₁ + W.b₂ / 12), (√(4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216))⁻¹ := by
  rw [leastRealPeriodIntegral, ← integral_comp_add_right_Ioi]
  refine congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_)
  rw [realPeriodIntegrand, ← W.eval_toPoly_twoTorsionPolynomial_sub (x + W.b₂ / 12),
    add_sub_cancel_right]

/- ## The real period as an integral -/

/-- **The real period as an integral**: the integral of $|\omega|$ over the identity component of
$E(\mathbb{R})$, multiplied by the number of connected components of $E(\mathbb{R})$. This is the
real period of the Birch and Swinnerton-Dyer conjecture. -/
def realPeriodIntegral : ℝ := (W.nrRealComponents : ℝ) * W.leastRealPeriodIntegral

/-- The real period of an elliptic curve over $\mathbb{R}$ is positive. -/
lemma realPeriodIntegral_pos [W.IsElliptic] : 0 < W.realPeriodIntegral :=
  mul_pos (Nat.cast_pos.mpr W.nrRealComponents_pos) W.leastRealPeriodIntegral_pos

/-- When $\Delta > 0$ the real period is twice the least positive real period. -/
lemma realPeriodIntegral_of_pos (h : 0 < W.Δ) :
    W.realPeriodIntegral = 2 * W.leastRealPeriodIntegral := by
  simp [realPeriodIntegral, W.nrRealComponents_of_pos h]

/-- When $\Delta < 0$ the real period is the least positive real period. -/
lemma realPeriodIntegral_of_neg (h : W.Δ < 0) :
    W.realPeriodIntegral = W.leastRealPeriodIntegral := by
  simp [realPeriodIntegral, W.nrRealComponents_of_neg h]

end WeierstrassCurve

end
