import WeilPrimeSummabilityV1
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The archimedean integral in the existing Weil normalization is integrable on
the repository's compact-smooth test-function domain.  The apparent singularity
at 1 is removed by a divided difference; compact support away from 0 makes the
tail a constant multiple of `(x^2 - 1)⁻¹`.

These are convergence statements.  No explicit-formula identity or sign
inequality is assumed or established here.
-/

open Set Complex MeasureTheory
open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-- Multiplying numerator and denominator by `x` exposes the quadratic tail. -/
theorem weil_archimedean_integrand_rational_v1 (f : ℝ → ℂ) {x : ℝ}
    (hx : 1 < x) :
    WeilArchimedeanIntegrandV1 f x =
      ((x : ℂ) * f x + f x⁻¹ - 2 * f 1) / ((x : ℂ) ^ 2 - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  have hq : (x : ℂ) ^ 2 - 1 ≠ 0 := by
    exact_mod_cast (show x ^ 2 - 1 ≠ 0 by nlinarith)
  have hd : (x : ℂ) - (x : ℂ)⁻¹ ≠ 0 := by
    have hi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have hr : x - x⁻¹ ≠ 0 := by linarith
    exact_mod_cast hr
  simp only [WeilArchimedeanIntegrandV1, Complex.ofReal_inv]
  field_simp [hx0, hq, hd]
  <;> ring

/-- The divided difference supplies the finite continuous extension at 1. -/
theorem weil_archimedean_integrand_dslope_v1 (f : ℝ → ℂ) {x : ℝ}
    (hx : 1 < x) :
    WeilArchimedeanIntegrandV1 f x =
      dslope (fun t : ℝ => (t : ℂ) * f t + f t⁻¹) 1 x / ((x : ℂ) + 1) := by
  rw [weil_archimedean_integrand_rational_v1 f hx,
    dslope_of_ne _ (ne_of_gt hx)]
  simp only [slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_sub, Complex.ofReal_one, inv_one, one_mul]
  have hm : (x : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (show x - 1 ≠ 0 by linarith)
  have hp : (x : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show x + 1 ≠ 0 by linarith)
  have hq : (x : ℂ) ^ 2 - 1 ≠ 0 := by
    exact_mod_cast (show x ^ 2 - 1 ≠ 0 by nlinarith)
  field_simp [hm, hp, hq]
  <;> ring

private theorem weil_archimedean_aux_differentiable_v1 (f : WeilCompactSmoothGV1)
    {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * f.1 t + f.1 t⁻¹) x := by
  have hf : Differentiable ℝ f.1 := f.2.1.differentiable (by simp)
  exact ((Complex.differentiable_ofReal x).mul (hf x)).add
    ((hf x⁻¹).comp x (differentiableAt_id.inv hx))

/-- Integrability across the apparent endpoint singularity, on every bounded interval. -/
theorem weil_compact_smooth_archimedean_integrableOn_Ioc_v1
    (f : WeilCompactSmoothGV1) (R : ℝ) :
    IntegrableOn (WeilArchimedeanIntegrandV1 f.1) (Ioc 1 R) := by
  let n : ℝ → ℂ := fun t => (t : ℂ) * f.1 t + f.1 t⁻¹
  have hs : ContinuousOn (dslope n 1) (Icc 1 R) := by
    intro x hx
    by_cases he : x = 1
    · subst x
      exact (continuousAt_dslope_same.mpr
        (weil_archimedean_aux_differentiable_v1 f one_ne_zero)).continuousWithinAt
    · apply (continuousWithinAt_dslope_of_ne he).mpr
      exact (weil_archimedean_aux_differentiable_v1 f
        (show x ≠ 0 by linarith [hx.1])).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun x : ℝ => dslope n 1 x / ((x : ℂ) + 1)) (Icc 1 R) := by
    apply hs.div (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
    intro x hx
    change (x : ℂ) + 1 ≠ 0
    exact_mod_cast (show x + 1 ≠ 0 by linarith [hx.1])
  refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun ?_
    measurableSet_Ioc
  intro x hx
  exact (weil_archimedean_integrand_dslope_v1 f.1 hx.1).symm

/-- The compact-support tail is bounded by an integrable inverse square. -/
theorem weil_archimedean_integrand_tail_bound_v1 (f : ℝ → ℂ) {x : ℝ}
    (hx : 2 ≤ x) (hz : f x = 0 ∧ f x⁻¹ = 0) :
    ‖WeilArchimedeanIntegrandV1 f x‖ ≤ (4 * ‖f 1‖) * x ^ (-2 : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hq : 0 < x ^ 2 - 1 := by nlinarith
  have hs : 0 < x ^ 2 := by nlinarith
  have he : WeilArchimedeanIntegrandV1 f x =
      -(2 * f 1) / (((x ^ 2 - 1 : ℝ) : ℂ)) := by
    rw [weil_archimedean_integrand_rational_v1 f hx1]
    simp only [hz.1, hz.2, mul_zero, zero_add, zero_sub, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_one]
  rw [he, norm_div, norm_neg, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  calc
    2 * ‖f 1‖ / (x ^ 2 - 1) ≤ 4 * ‖f 1‖ / x ^ 2 := by
      apply (div_le_div_iff₀ hq hs).mpr
      have hnon : 0 ≤ ‖f 1‖ * (x ^ 2 - 2) :=
        mul_nonneg (norm_nonneg _) (by nlinarith)
      nlinarith
    _ = (4 * ‖f 1‖) * x ^ (-2 : ℝ) := by
      simp [Real.rpow_neg_ofNat, zpow_neg, div_eq_mul_inv]

/-- The existing archimedean integrand is integrable for every existing test function. -/
theorem weil_compact_smooth_archimedean_integrable_v1 (f : WeilCompactSmoothGV1) :
    IntegrableOn (WeilArchimedeanIntegrandV1 f.1) (Ioi 1) := by
  obtain ⟨R, hR, hz⟩ := weil_compact_smooth_eventually_zero_and_inv_v1 f
  have hRp : 0 < R := by linarith
  have hc : ContinuousOn (WeilArchimedeanIntegrandV1 f.1) (Ioi R) := by
    have hcq : ContinuousOn
        (fun x : ℝ => ((x : ℂ) * f.1 x + f.1 x⁻¹ - 2 * f.1 1) /
          ((x : ℂ) ^ 2 - 1)) (Ioi R) := by
      intro x hx
      change R < x at hx
      have hxp : 1 < x := by linarith [hx]
      have hn := (weil_archimedean_aux_differentiable_v1 f
        (show x ≠ 0 by linarith)).continuousAt
      have hd : (x : ℂ) ^ 2 - 1 ≠ 0 := by
        exact_mod_cast (show x ^ 2 - 1 ≠ 0 by nlinarith)
      exact ((hn.sub continuousAt_const).div
        ((Complex.continuous_ofReal.continuousAt.pow 2).sub continuousAt_const)
        hd).continuousWithinAt
    apply hcq.congr
    intro x hx
    change R < x at hx
    exact weil_archimedean_integrand_rational_v1 f.1 (x := x) (by linarith)
  have hp : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hRp
  have ht : IntegrableOn (WeilArchimedeanIntegrandV1 f.1) (Ioi R) := by
    apply (hp.const_mul (4 * ‖f.1 1‖)).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact weil_archimedean_integrand_tail_bound_v1 f.1
      (hR.trans (le_of_lt hx)) (hz x (le_of_lt hx))
  have hu := integrableOn_union.mpr
    ⟨weil_compact_smooth_archimedean_integrableOn_Ioc_v1 f R, ht⟩
  apply hu.mono_set
  intro x hx
  by_cases hxR : x ≤ R
  · exact Or.inl ⟨hx, hxR⟩
  · exact Or.inr (lt_of_not_ge hxR)

/-- Both explicit right-side convergence obligations are now discharged on the
repository's compact-smooth domain; the identity with zeros is a separate theorem. -/
theorem weil_compact_smooth_explicit_right_side_convergent_v1
    (f : WeilCompactSmoothGV1) : WeilExplicitRightSideConvergentV1 f.1 := by
  exact ⟨weil_compact_smooth_prime_summable_v1 f,
    weil_compact_smooth_archimedean_integrable_v1 f⟩
