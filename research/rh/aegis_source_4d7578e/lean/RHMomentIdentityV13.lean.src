import WeilAutocorrelationPoleAggregationV1
import Mathlib.Tactic

/-!
AEGIS Ω — the moment identity in log coordinates, V13.

For `g : WeilCompactSmoothGV1` with `A = WeilAutocorrelationV1 g` this module proves

* `moment_log_integrableOn`: `u ↦ e^u · Re A(e^u) · (1 + e^{-u})` is integrable on `(0, ∞)`;
* `moment_log_identity`: under `WeilMomentConditionsV1 g`,

      ∫_{u > 0} e^u · Re A(e^u) · (1 + e^{-u}) du = 0.

Route.  The pole-term theorem `mellin A 0 + mellin A 1 = 0` is the statement
`∫_{x>0} (1 + x⁻¹) A(x) dx = 0`.  Split at `x = 1`.  The substitution `x ↦ x⁻¹`
(`integral_comp_rpow_Ioi` with `p = -1`) and the reciprocal law
`A(x⁻¹) = x · conj A(x)` turn the `(0,1]` half into the complex conjugate of the
`(1,∞)` half, so the total is `2 · Re` of the `(1,∞)` half.  The substitution
`x = e^u` (`integral_comp_exp_Ioi`) rewrites that half in log coordinates.

Not RH.  No sign of the Weil functional is asserted.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMomentIdentityV13

/-- The combined Mellin integrand `(1 + x⁻¹) A(x)`. -/
def momentIntegrand (g : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  WeilAutocorrelationV1 g x + (x : ℂ)⁻¹ * WeilAutocorrelationV1 g x

theorem mellin_convergent_autocorrelation (g : WeilCompactSmoothGV1) (s : ℂ) :
    MellinConvergent (WeilAutocorrelationV1 g) s :=
  weil_compact_smooth_mellin_convergent_all_v1 (WeilAutocorrelationCompactSmoothV1 g) s

theorem cpow_zero_sub_one (x : ℝ) : (x : ℂ) ^ ((0 : ℂ) - 1) = (x : ℂ)⁻¹ := by
  rw [zero_sub, Complex.cpow_neg_one]

theorem cpow_one_sub_one (x : ℝ) : (x : ℂ) ^ ((1 : ℂ) - 1) = 1 := by
  rw [sub_self, Complex.cpow_zero]

theorem momentIntegrand_integrableOn (g : WeilCompactSmoothGV1) :
    IntegrableOn (momentIntegrand g) (Ioi (0 : ℝ)) := by
  have h0 := mellin_convergent_autocorrelation g 0
  have h1 := mellin_convergent_autocorrelation g 1
  rw [MellinConvergent] at h0 h1
  simp only [cpow_zero_sub_one, cpow_one_sub_one, smul_eq_mul, one_mul] at h0 h1
  exact h1.add h0

theorem momentIntegrand_integral_zero (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    ∫ x in Ioi (0 : ℝ), momentIntegrand g x = 0 := by
  have h0 := mellin_convergent_autocorrelation g 0
  have h1 := mellin_convergent_autocorrelation g 1
  rw [MellinConvergent] at h0 h1
  have hp := weil_moment_conditions_autocorrelation_pole_term_zero_v1 g hm
  unfold mellin at hp
  rw [← integral_add h0 h1] at hp
  rw [← hp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [momentIntegrand, cpow_zero_sub_one, cpow_one_sub_one, smul_eq_mul]
  ring

/-- Pointwise reflection: `x⁻² · F(x⁻¹) = conj F(x)` for `x > 0`. -/
theorem reflect_pointwise (g : WeilCompactSmoothGV1) {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • momentIntegrand g x⁻¹ =
      conj (momentIntegrand g x) := by
  have hr : x ^ ((-1 : ℝ) - 1) = (x ^ 2)⁻¹ := by
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx.le, Real.rpow_two]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [hr]
  unfold momentIntegrand
  rw [weil_autocorrelation_reciprocal_v1 g hx]
  simp only [abs_neg, abs_one, one_mul, Complex.real_smul, map_add, map_mul, map_inv₀,
    Complex.conj_ofReal, Complex.ofReal_inv, Complex.ofReal_pow, inv_inv]
  field_simp
  ring

/-- The `(0,1]` half is the conjugate of the `(1,∞)` half. -/
theorem integral_Ioc_eq_conj (g : WeilCompactSmoothGV1) :
    ∫ x in Ioc (0 : ℝ) 1, momentIntegrand g x =
      conj (∫ x in Ioi (1 : ℝ), momentIntegrand g x) := by
  have key := integral_comp_rpow_Ioi ((Iic (1 : ℝ)).indicator (momentIntegrand g))
    (p := -1) (by norm_num)
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic] at key
  have hIci : ∫ x in Ici (1 : ℝ), conj (momentIntegrand g x) =
      ∫ x in Ioi (1 : ℝ), conj (momentIntegrand g x) := integral_Ici_eq_integral_Ioi
  rw [← key, ← integral_conj, ← hIci]
  have hs : Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 :=
    Set.inter_eq_right.mpr (Ici_subset_Ioi.mpr zero_lt_one)
  rw [← hs, ← setIntegral_indicator measurableSet_Ici]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx : (0 : ℝ) < x := hx
  rw [Real.rpow_neg_one]
  by_cases h1 : 1 ≤ x
  · have hmem : x⁻¹ ∈ Iic (1 : ℝ) := (inv_le_one₀ hx).mpr h1
    rw [indicator_of_mem hmem, indicator_of_mem (show x ∈ Ici (1 : ℝ) from h1)]
    exact reflect_pointwise g hx
  · have hmem : x⁻¹ ∉ Iic (1 : ℝ) := fun h => h1 ((inv_le_one₀ hx).mp h)
    rw [indicator_of_notMem hmem, indicator_of_notMem (show x ∉ Ici (1 : ℝ) from h1),
      smul_zero]

theorem integral_Ioi_one_eq (g : WeilCompactSmoothGV1) :
    ∫ x in Ioi (1 : ℝ), momentIntegrand g x =
      ∫ u in Ioi (0 : ℝ), Real.exp u • momentIntegrand g (Real.exp u) := by
  have h := integral_comp_exp_Ioi (momentIntegrand g) 0
  rw [Real.exp_zero] at h
  exact h.symm

theorem log_integrableOn (g : WeilCompactSmoothGV1) :
    IntegrableOn (fun u : ℝ => Real.exp u • momentIntegrand g (Real.exp u)) (Ioi (0 : ℝ)) := by
  rw [integrableOn_comp_exp_Ioi, Real.exp_zero]
  exact (momentIntegrand_integrableOn g).mono_set (Ioi_subset_Ioi zero_le_one)

theorem log_integrand_re (g : WeilCompactSmoothGV1) (u : ℝ) :
    (Real.exp u • momentIntegrand g (Real.exp u)).re =
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re * (1 + Real.exp (-u)) := by
  unfold momentIntegrand
  rw [Complex.smul_re, Complex.add_re, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    Real.exp_neg, smul_eq_mul]
  ring

theorem moment_log_integrableOn (g : WeilCompactSmoothGV1) :
    IntegrableOn (fun u : ℝ => Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re *
        (1 + Real.exp (-u)))
      (Ioi (0 : ℝ)) := by
  have h := (log_integrableOn g).re
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  exact log_integrand_re g u

theorem moment_log_identity (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∫ u in Ioi (0 : ℝ), Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re *
        (1 + Real.exp (-u)) = 0 := by
  have hF := momentIntegrand_integrableOn g
  have hsplit : ∫ x in Ioi (0 : ℝ), momentIntegrand g x =
      (∫ x in Ioc (0 : ℝ) 1, momentIntegrand g x) +
        ∫ x in Ioi (1 : ℝ), momentIntegrand g x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi zero_le_one))]
  have h0 := momentIntegrand_integral_zero g hm
  rw [hsplit, integral_Ioc_eq_conj] at h0
  have hre : (∫ x in Ioi (1 : ℝ), momentIntegrand g x).re = 0 := by
    have := congrArg Complex.re h0
    rw [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  calc
    (∫ u in Ioi (0 : ℝ), Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re *
        (1 + Real.exp (-u)))
        = ∫ u in Ioi (0 : ℝ), (Real.exp u • momentIntegrand g (Real.exp u)).re := by
          congr 1
          funext u
          exact (log_integrand_re g u).symm
    _ = (∫ u in Ioi (0 : ℝ), Real.exp u • momentIntegrand g (Real.exp u)).re :=
          integral_re (log_integrableOn g)
    _ = 0 := by rw [← integral_Ioi_one_eq]; exact hre

end AEGIS.RHMomentIdentityV13

#print axioms AEGIS.RHMomentIdentityV13.moment_log_integrableOn
#print axioms AEGIS.RHMomentIdentityV13.moment_log_identity
