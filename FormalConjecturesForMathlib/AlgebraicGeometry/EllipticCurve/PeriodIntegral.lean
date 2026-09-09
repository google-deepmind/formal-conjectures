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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public noncomputable section

/-!
# The real period of an elliptic curve as an integral

Let $E$ be an elliptic curve over $\mathbb{R}$ with Weierstrass equation
$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ and invariant differential
$\omega = \frac{dx}{2y + a_1 x + a_3}$. Completing the square,
$(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6 =: F(x)$, the *2-division polynomial*
`WeierstrassCurve.Ψ₂Sq`. The real locus $E(\mathbb{R})$ consists of the point at
infinity and the real points with $F(x) \geq 0$; over $F(x) > 0$ it has the two branches
$2y + a_1 x + a_3 = \pm\sqrt{F(x)}$, on each of which $|\omega| = \frac{dx}{\sqrt{F(x)}}$. Hence
the **real period** of the Birch and Swinnerton-Dyer conjecture is
$$\Omega_E = \int_{E(\mathbb{R})} |\omega| = 2 \int_{\mathbb{R}} \frac{dx}{\sqrt{F(x)}},$$
with the integrand taken to be $0$ where $F \leq 0$.

This file defines
* `WeierstrassCurve.realPeriodIntegrand`, the density $x \mapsto 1 / \sqrt{F(x)}$, with the junk
  value $0$ where $F \leq 0$;
* `WeierstrassCurve.realPeriodIntegral`, the real period $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$;
* `WeierstrassCurve.leastRealPeriodIntegral`, the integral $2 \int_{e_1}^\infty dx / \sqrt{F(x)}$
  over the identity component $E(\mathbb{R})^0 = \{x \geq e_1\} \cup \{O\}$, the least positive
  real period of the period lattice, where $e_1$ is the largest real root `WeierstrassCurve.e₁`
  of $F$;

and proves that for an elliptic curve the integrand is integrable
(`WeierstrassCurve.integrable_realPeriodIntegrand`) and that
$$\Omega_E = c_\infty \cdot 2 \int_{e_1}^\infty \frac{dx}{\sqrt{F(x)}},$$
where $c_\infty$ is $2$ if $\Delta > 0$ (`WeierstrassCurve.realPeriodIntegral_of_pos`) and $1$
if $\Delta < 0$ (`WeierstrassCurve.realPeriodIntegral_of_neg`), so that the real period is
positive (`WeierstrassCurve.realPeriodIntegral_pos`). The real roots of $F$ are described in
`FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Real`: when
$\Delta < 0$ it has the single real root $e_1$ (`WeierstrassCurve.eq_e₁_of_isRoot_of_neg`) and
the integrand vanishes on $(-\infty, e_1]$; when $\Delta > 0$ it has three real roots
$e_3 < e_2 < e_1$ (`WeierstrassCurve.exists_three_roots_of_pos`) and the bounded component
$\{e_3 \leq x \leq e_2\}$ contributes as much as the identity component, the second equality in
DLMF 23.6.34: translation by the two-torsion point $(e_2, 0)$ maps $E(\mathbb{R})^0$ onto the
bounded component and preserves $\omega$. On $x$-coordinates it is the involution
`WeierstrassCurve.ovalMap`, $x \mapsto e_2 - (e_1 - e_2)(e_2 - e_3) / (x - e_2)$, exchanging
$(e_1, \infty)$ and $(e_3, e_2)$ with $F(\varphi(x)) = \varphi'(x)^2 F(x)$
(`WeierstrassCurve.setIntegral_realPeriodIntegrand_Ioo`).

*Convention.* `WeierstrassCurve.realPeriodIntegral` is $\int_{E(\mathbb{R})} |\omega|$, the
LMFDB convention, which absorbs the real Tamagawa number $c_\infty$, the number of connected
components of $E(\mathbb{R})$. A Birch and Swinnerton-Dyer statement using it must therefore take
the Tamagawa product over the *finite* places only. The other convention pairs
`WeierstrassCurve.leastRealPeriodIntegral` with a product over *all* places. The two give the same
number, but mixing them miscounts by a factor of $2$ when $\Delta > 0$.

*References:*
- [LMFDB](https://beta.lmfdb.org/knowledge/show/ec.period), knowls `ec.period`,
  `ec.q.real_period` and `ec.q.period_lattice`
- [DLMF](https://dlmf.nist.gov/23.6.iv), §23.5 and §23.6(iv), equations 23.6.34 and 23.6.36
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Sil1994] Joseph H. Silverman. Advanced Topics in the Arithmetic of Elliptic Curves,
    Chapter V §2, https://link.springer.com/book/10.1007/978-1-4612-0851-8
-/

open Filter MeasureTheory Polynomial Set

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

variable {e₂ e₃ : ℝ}

/- ## The integrand -/

/-- The density $|\omega| / dx = 1 / \sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}$ of the invariant
differential on either branch of the real locus, as a function on $\mathbb{R}$, with the junk value
$0$ where the cubic is not positive. -/
def realPeriodIntegrand (x : ℝ) : ℝ := (√(W.Ψ₂Sq.eval x))⁻¹

lemma realPeriodIntegrand_nonneg (x : ℝ) : 0 ≤ W.realPeriodIntegrand x :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma realPeriodIntegrand_pos {x : ℝ} (hx : W.e₁ < x) : 0 < W.realPeriodIntegrand x :=
  inv_pos.mpr (Real.sqrt_pos.mpr (W.eval_Ψ₂Sq_pos hx))

lemma realPeriodIntegrand_eq_zero {x : ℝ} (hx : W.Ψ₂Sq.eval x ≤ 0) :
    W.realPeriodIntegrand x = 0 := by
  rw [realPeriodIntegrand, Real.sqrt_eq_zero_of_nonpos hx, inv_zero]

lemma realPeriodIntegrand_eq_zero_of_le_e₁ (h : W.Δ < 0) {x : ℝ} (hx : x ≤ W.e₁) :
    W.realPeriodIntegrand x = 0 :=
  W.realPeriodIntegrand_eq_zero <| W.eval_Ψ₂Sq_nonpos fun _ hr ↦
    W.eq_e₁_of_isRoot_of_neg h hr ▸ hx

lemma realPeriodIntegrand_eq_zero_of_factor (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.Ψ₂Sq = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))))
    {x : ℝ} (hx : x ≤ W.e₁) (hx' : x ∉ Ioo e₃ e₂) : W.realPeriodIntegrand x = 0 := by
  apply W.realPeriodIntegrand_eq_zero
  rw [W.eval_Ψ₂Sq_of_factor hF]
  rcases not_and_or.mp hx' with h | h <;> rw [not_lt] at h
  · nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ W.e₁ - x by linarith)
      (show 0 ≤ e₂ - x by linarith)) (show 0 ≤ e₃ - x by linarith)]
  · nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ W.e₁ - x by linarith)
      (show 0 ≤ x - e₂ by linarith)) (show 0 ≤ x - e₃ by linarith)]

lemma measurable_realPeriodIntegrand : Measurable W.realPeriodIntegrand :=
  (Real.continuous_sqrt.comp W.Ψ₂Sq.continuous).measurable.inv

/- ## Integrability on the identity component -/

lemma integrableOn_realPeriodIntegrand_Ioi {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c ≤ x → x ^ 3 ≤ W.Ψ₂Sq.eval x) :
    IntegrableOn W.realPeriodIntegrand (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hc).mono'
    W.measurable_realPeriodIntegrand.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have : x ^ (-3 / 2 : ℝ) = (√(x ^ 3))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul (hc.trans hx).le,
        ← Real.rpow_neg (hc.trans hx).le]
    grind
  rw [Real.norm_eq_abs, abs_of_nonneg (W.realPeriodIntegrand_nonneg x), this]
  exact inv_anti₀ (Real.sqrt_pos.mpr (by simp [hc.trans hx])) (Real.sqrt_le_sqrt (h x hx.le))

lemma integrableOn_realPeriodIntegrand_Ioc [W.IsElliptic] {c : ℝ} (hc : W.e₁ ≤ c) :
    IntegrableOn W.realPeriodIntegrand (Ioc W.e₁ c) := by
  obtain ⟨Q, hQ, hQpos⟩ := W.exists_Ψ₂Sq_eq_X_sub_C_mul
  have hr : IntegrableOn (fun x : ℝ ↦ (x - W.e₁) ^ (-(1 / 2) : ℝ)) (Icc W.e₁ c) := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp ?_
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c - W.e₁)
        (by norm_num)).comp_sub_right W.e₁
  refine ((hr.mul_continuousOn ((Real.continuous_sqrt.comp Q.continuous).continuousOn.inv₀
    fun x hx ↦ (Real.sqrt_pos.mpr (hQpos x hx.1)).ne') isCompact_Icc).mono_set
    Ioc_subset_Icc_self).congr_fun (fun x hx ↦ ?_) measurableSet_Ioc
  simp only [Pi.inv_apply, Function.comp_apply, realPeriodIntegrand, hQ, eval_mul, eval_sub, eval_X,
    eval_C, Real.sqrt_mul (sub_nonneg.mpr hx.1.le), mul_inv, Real.rpow_neg (sub_nonneg.mpr hx.1.le),
    ← Real.sqrt_eq_rpow]

lemma integrableOn_realPeriodIntegrand [W.IsElliptic] :
    IntegrableOn W.realPeriodIntegrand (Ioi W.e₁) := by
  obtain ⟨_, hR₀⟩ := eventually_atTop.mp W.eventually_pow_three_le_eval_Ψ₂Sq
  rw [← Ioc_union_Ioi_eq_Ioi (le_max_of_le_right (le_max_left _ _))]
  exact (W.integrableOn_realPeriodIntegrand_Ioc (le_max_of_le_right (le_max_left _ _))).union
    (W.integrableOn_realPeriodIntegrand_Ioi (zero_lt_one.trans_le (le_max_of_le_right
    (le_max_right _ _))) fun x hx ↦ hR₀ x ((le_max_left _ _).trans hx))

/- ## Translation by a two-torsion point -/

/-- The $x$-coordinate of translation by the two-torsion point $(e_2, 0)$, for a cubic with real
roots $e_3 < e_2 < e_1$: the involution $x \mapsto e_2 - (e_1 - e_2)(e_2 - e_3) / (x - e_2)$,
which exchanges the identity component $(e_1, \infty)$ and the bounded component $(e_3, e_2)$. -/
def ovalMap (e₁ e₂ e₃ x : ℝ) : ℝ := e₂ - (e₁ - e₂) * (e₂ - e₃) / (x - e₂)

section ovalMap

variable {e₁ : ℝ}

lemma hasDerivAt_ovalMap {x : ℝ} (hx : x ≠ e₂) :
    HasDerivAt (ovalMap e₁ e₂ e₃) ((e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2) x :=
    ((((((hasDerivAt_id' x).sub_const e₂).inv (sub_ne_zero.mpr hx)).const_mul
    ((e₁ - e₂) * (e₂ - e₃))).const_sub e₂).congr_deriv (by ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun y ↦ (by simp [ovalMap, div_eq_mul_inv]))

lemma ovalMap_ovalMap (hk : (e₁ - e₂) * (e₂ - e₃) ≠ 0) (x : ℝ) :
    ovalMap e₁ e₂ e₃ (ovalMap e₁ e₂ e₃ x) = x := by
  grind [ovalMap, ovalMap, sub_sub_cancel_left, div_neg, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ hk]

lemma ovalMap_mem_Ioo (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) {x : ℝ} (hx : e₁ < x) :
    ovalMap e₁ e₂ e₃ x ∈ Ioo e₃ e₂ := by
  have h : 0 < (e₁ - e₂) * (e₂ - e₃) := mul_pos (by linarith) (by linarith)
  have : (e₁ - e₂) * (e₂ - e₃) / (x - e₂) < e₂ - e₃ := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left (show e₁ - e₂ < x - e₂ by linarith)
      (show 0 < e₂ - e₃ by linarith)]
  constructor <;> (rw [ovalMap]; linarith [div_pos h (show 0 < x - e₂ by linarith)])

lemma lt_ovalMap (h₂₁ : e₂ < e₁) {y : ℝ} (hy : y ∈ Ioo e₃ e₂) : e₁ < ovalMap e₁ e₂ e₃ y := by
  have : e₁ - e₂ < (e₁ - e₂) * (e₂ - e₃) / (e₂ - y) := by
    rw [lt_div_iff₀ (by linarith [hy.2])]
    nlinarith [mul_lt_mul_of_pos_left (show e₂ - y < e₂ - e₃ by linarith [hy.1])
      (show 0 < e₁ - e₂ by linarith)]
  rw [ovalMap, show y - e₂ = -(e₂ - y) by ring, div_neg]
  linarith

lemma image_ovalMap_Ioi (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    ovalMap e₁ e₂ e₃ '' Ioi e₁ = Ioo e₃ e₂ := by
  refine subset_antisymm ?_ fun y hy ↦ ⟨ovalMap e₁ e₂ e₃ y, lt_ovalMap h₂₁ hy, ovalMap_ovalMap
    ((mul_pos (by linarith) (by linarith)).ne') y⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ovalMap_mem_Ioo h₃₂ h₂₁ hx

lemma injOn_ovalMap (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) : InjOn (ovalMap e₁ e₂ e₃) (Ioi e₁) := by
  have : (e₁ - e₂) * (e₂ - e₃) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  intro x _ y _ hxy
  rw [← ovalMap_ovalMap this x, hxy, ovalMap_ovalMap this y]

lemma abs_mul_inv_sqrt_ovalMap (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) {x : ℝ} (hx : e₁ < x) :
    |(e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2| *
    (√(4 * (ovalMap e₁ e₂ e₃ x - e₁) * (ovalMap e₁ e₂ e₃ x - e₂) * (ovalMap e₁ e₂ e₃ x - e₃)))⁻¹ =
    (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ := by
  have : x - e₂ ≠ 0 := sub_ne_zero.mpr (h₂₁.trans hx).ne'
  set c := (e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2 with hc
  have h : 0 < c := div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have : 4 * (ovalMap e₁ e₂ e₃ x - e₁) * (ovalMap e₁ e₂ e₃ x - e₂) *
      (ovalMap e₁ e₂ e₃ x - e₃) = c ^ 2 * (4 * (x - e₁) * (x - e₂) * (x - e₃)) := by
    simp only [ovalMap, hc]
    field_simp; ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq h.le, abs_of_pos h, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]

end ovalMap

/- ## The bounded component -/

lemma setIntegral_realPeriodIntegrand_Ioo (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.Ψ₂Sq = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃)))) :
    ∫ x in Ioo e₃ e₂, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  rw [← image_ovalMap_Ioi h₃₂ h₂₁, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx ↦ (hasDerivAt_ovalMap (h₂₁.trans hx).ne').hasDerivWithinAt) (injOn_ovalMap h₃₂ h₂₁)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simpa [smul_eq_mul, realPeriodIntegrand, W.eval_Ψ₂Sq_of_factor hF] using
    abs_mul_inv_sqrt_ovalMap h₃₂ h₂₁ hx

lemma integrableOn_realPeriodIntegrand_Ioo [W.IsElliptic] (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.Ψ₂Sq = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃)))) :
    IntegrableOn W.realPeriodIntegrand (Ioo e₃ e₂) := by
  rw [← image_ovalMap_Ioi h₃₂ h₂₁, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun x hx ↦ (hasDerivAt_ovalMap (h₂₁.trans hx).ne').hasDerivWithinAt)
    (injOn_ovalMap h₃₂ h₂₁)]
  refine W.integrableOn_realPeriodIntegrand.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  simpa [smul_eq_mul, realPeriodIntegrand, W.eval_Ψ₂Sq_of_factor hF] using
    (abs_mul_inv_sqrt_ovalMap h₃₂ h₂₁ hx).symm

/- ## Integrability on the whole line -/

lemma integrableOn_realPeriodIntegrand_Iic_of_neg (h : W.Δ < 0) :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) :=
  integrableOn_zero.congr_fun (fun _ hx ↦ (W.realPeriodIntegrand_eq_zero_of_le_e₁ h hx).symm)
    measurableSet_Iic

lemma setIntegral_realPeriodIntegrand_Iic_of_neg (h : W.Δ < 0) :
    ∫ x in Iic W.e₁, W.realPeriodIntegrand x = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun _ hx ↦ W.realPeriodIntegrand_eq_zero_of_le_e₁ h hx

lemma integrableOn_realPeriodIntegrand_Iic_of_pos (h : 0 < W.Δ) :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne'⟩
  obtain ⟨e₂, e₃, h₃₂, h₂₁, hF⟩ := W.exists_three_roots_of_pos h
  exact (W.integrableOn_realPeriodIntegrand_Ioo h₃₂ h₂₁ hF).of_forall_sdiff_eq_zero
    measurableSet_Iic fun x hx ↦ W.realPeriodIntegrand_eq_zero_of_factor h₃₂ h₂₁ hF hx.1 hx.2

lemma setIntegral_realPeriodIntegrand_Iic_of_pos (h : 0 < W.Δ) :
    ∫ x in Iic W.e₁, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  obtain ⟨_, _, h₃₂, h₂₁, hF⟩ := W.exists_three_roots_of_pos h
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
    (fun x hx ↦ (hx.2.trans h₂₁).le) (fun x hx ↦ W.realPeriodIntegrand_eq_zero_of_factor h₃₂ h₂₁
    hF hx.1 hx.2), W.setIntegral_realPeriodIntegrand_Ioo h₃₂ h₂₁ hF]

lemma integrableOn_realPeriodIntegrand_Iic [W.IsElliptic] :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) := by
  rcases lt_or_gt_of_ne (isUnit_iff_ne_zero.mp W.isUnit_Δ) with h | h
  · exact W.integrableOn_realPeriodIntegrand_Iic_of_neg h
  · exact W.integrableOn_realPeriodIntegrand_Iic_of_pos h

theorem integrable_realPeriodIntegrand [W.IsElliptic] : Integrable W.realPeriodIntegrand := by
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  exact W.integrableOn_realPeriodIntegrand_Iic.union W.integrableOn_realPeriodIntegrand

lemma integral_realPeriodIntegrand_eq_add [W.IsElliptic] : ∫ x, W.realPeriodIntegrand x =
    (∫ x in Iic W.e₁, W.realPeriodIntegrand x) + ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  rw [← setIntegral_univ, ← Iic_union_Ioi, setIntegral_union (Iic_disjoint_Ioi le_rfl)
    measurableSet_Ioi W.integrableOn_realPeriodIntegrand_Iic W.integrableOn_realPeriodIntegrand]

theorem integral_realPeriodIntegrand_of_neg (h : W.Δ < 0) :
    ∫ x, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne⟩
  rw [W.integral_realPeriodIntegrand_eq_add, W.setIntegral_realPeriodIntegrand_Iic_of_neg h,
    zero_add]

theorem integral_realPeriodIntegrand_of_pos (h : 0 < W.Δ) :
    ∫ x, W.realPeriodIntegrand x = 2 * ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne'⟩
  rw [W.integral_realPeriodIntegrand_eq_add, W.setIntegral_realPeriodIntegrand_Iic_of_pos h,
    two_mul]

/- ## The least positive real period as an integral -/

/-- The least positive real period as an integral,
$2 \int_{e_1}^\infty \frac{dx}{\sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}}$: the integral of $|\omega|$
over the identity component of $E(\mathbb{R})$. -/
def leastRealPeriodIntegral : ℝ := 2 * ∫ x in Ioi W.e₁, W.realPeriodIntegrand x

lemma leastRealPeriodIntegral_pos [W.IsElliptic] : 0 < W.leastRealPeriodIntegral := by
  refine mul_pos two_pos ?_
  have : Function.support W.realPeriodIntegrand ∩ Ioi W.e₁ = Ioi W.e₁ :=
    inter_eq_right.mpr fun x hx ↦ (W.realPeriodIntegrand_pos hx).ne'
  simp [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall W.realPeriodIntegrand_nonneg)
    W.integrableOn_realPeriodIntegrand, this , Real.volume_Ioi]

/- ## The real period as an integral -/

/-- **The real period as an integral**: the integral of $|\omega|$ over the real locus
$E(\mathbb{R})$, that is $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$ with the integrand taken to be
$0$ where $F \leq 0$. This is the real period of the Birch and Swinnerton-Dyer conjecture, in the
convention that absorbs the real Tamagawa number. -/
def realPeriodIntegral : ℝ := 2 * ∫ x, W.realPeriodIntegrand x

theorem realPeriodIntegral_of_pos (h : 0 < W.Δ) :
    W.realPeriodIntegral = 2 * W.leastRealPeriodIntegral := by
  rw [realPeriodIntegral, W.integral_realPeriodIntegrand_of_pos h, leastRealPeriodIntegral]

theorem realPeriodIntegral_of_neg (h : W.Δ < 0) :
    W.realPeriodIntegral = W.leastRealPeriodIntegral := by
  rw [realPeriodIntegral, W.integral_realPeriodIntegrand_of_neg h, leastRealPeriodIntegral]

lemma realPeriodIntegral_pos [W.IsElliptic] : 0 < W.realPeriodIntegral := by
  rcases lt_or_gt_of_ne (isUnit_iff_ne_zero.mp W.isUnit_Δ) with h | h
  · simpa [W.realPeriodIntegral_of_neg h] using W.leastRealPeriodIntegral_pos
  · simpa [W.realPeriodIntegral_of_pos h] using mul_pos two_pos W.leastRealPeriodIntegral_pos

end WeierstrassCurve
