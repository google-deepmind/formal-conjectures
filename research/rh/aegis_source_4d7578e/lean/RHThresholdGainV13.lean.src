import RHHalfCapGainV13
import Mathlib.Tactic

/-!
AEGIS Ω — the half-cap moment gain with a free kernel threshold, V13.

`RHHalfCapGainV13` subtracts `lamR r · (moment integrand)`, whose kernel changes sign
exactly at the half-width `r`.  Here the multiplier is `lamR t` for any `0 < t ≤ r`, so
the kernel changes sign at `t`.  The pieces are bounded by

* `(0, t]`:   kernel `≥ 0`, `h(u) ≤ e^{u/2}E`                 (`inner_integral_le`);
* `(t, r]`:   kernel `≤ 0`, `h(u) ≥ −e^{u/2}E`                (`middle_majorant`);
* `(r, 2r]`:  kernel `≤ 0`, `h(u) ≥ −e^{u/2}E/2`  (half-cap, `half_cap_exp_re_lower`);
* `(2r, ∞)`:  `h = 0`.

Result, below `log 2`: `Re RHS(A) ≤ thrGain t r · E` with

  thrGain t r = κ + (t/2)e^{t/2} + lamR t·(2 sinh r + 2 sinh(r/2) − 8 sinh(t/2))
                − 2·cothTail t + ½·cothTail r + ½·cothTail(2r),

and `thrGain r r = halfGain r`.  The optimal threshold is `t ≈ 0.78 r`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHThresholdGainV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentGainV13
open AEGIS.RHHalfCapV13

/-- The threshold gain: kernel threshold `t`, log-half-width `r`. -/
def thrGain (t r : ℝ) : ℝ :=
  diagonalKappaV21 + (t / 2) * Real.exp (t / 2)
    + lamR t * (2 * Real.sinh r + 2 * Real.sinh (r / 2) - 8 * Real.sinh (t / 2))
    - 2 * cothTail t + cothTail r / 2 + cothTail (2 * r) / 2

/-- Half-cap majorant with the kernel threshold `t ≤ r`, on `(r, ∞)`. -/
theorem half_majorant_t (g : WeilCompactSmoothGV1) (t r a u : ℝ) (ht0 : 0 < t) (htr : t ≤ r)
    (hw : HalfWidthAt g r a) (hru : r < u) :
    budgetIntegrand g t u ≤
      lamR t * energy g.1 * Real.cosh (u / 2) - (3 / 2) * energy g.1 * (1 / Real.sinh u) := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := by linarith
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos t u ht0 (by linarith)
  have hh := half_cap_exp_re_lower g r a u hw hru
  have h1 := mul_le_mul_of_nonpos_right hh hk
  have h4 := exp_half_mul u
  have hge : 0 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    apply mul_nonneg hE (div_nonneg _ hsu.le)
    linarith [Real.one_le_exp (by linarith : (0 : ℝ) ≤ u / 2)]
  have h2 : -(Real.exp (u / 2) * (energy g.1 / 2)) *
        (1 / Real.sinh u - lamR t * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      (lamR t / 2) * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) -
        (3 / 2) * energy g.1 * (1 / Real.sinh u) -
        (1 / 2) * (energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u)) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  nlinarith

/-- Full-cap piece `(t, r]`. -/
theorem full_integral_le_t (g : WeilCompactSmoothGV1) (t r : ℝ) (ht0 : 0 < t) (htr : t ≤ r) :
    (∫ u in Ioc t r, budgetIntegrand g t u) ≤
      4 * lamR t * energy g.1 * (Real.sinh (r / 2) - Real.sinh (t / 2)) -
        2 * energy g.1 * (cothTail t - cothTail r) := by
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc t r) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans ht0 hu.1)
  have hA := (cosh_half_integrableOn t r).const_mul (2 * lamR t * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc t r ht0).const_mul (2 * energy g.1)
  calc
    _ ≤ ∫ u in Ioc t r, (2 * lamR t * energy g.1 * Real.cosh (u / 2) -
          2 * energy g.1 * (1 / Real.sinh u)) := by
      apply setIntegral_mono_on hI (hA.sub hB) measurableSet_Ioc
      intro u hu
      exact middle_majorant g t u ht0 hu.1.le
    _ = _ := by
      rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
        integral_cosh_half t r htr, integral_inv_sinh_Ioc t r ht0 htr]
      ring

/-- Half-cap piece `(r, 2r]`. -/
theorem half_integral_le_t (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t) (htr : t ≤ r)
    (hw : HalfWidthAt g r a) :
    (∫ u in Ioc r (2 * r), budgetIntegrand g t u) ≤
      2 * lamR t * energy g.1 * (Real.sinh r - Real.sinh (r / 2)) -
        (3 / 2) * energy g.1 * (cothTail r - cothTail (2 * r)) := by
  have hr0 : 0 < r := lt_of_lt_of_le ht0 htr
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc r (2 * r)) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans hr0 hu.1)
  have hA := (cosh_half_integrableOn r (2 * r)).const_mul (lamR t * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc r (2 * r) hr0).const_mul ((3 / 2) * energy g.1)
  calc
    _ ≤ ∫ u in Ioc r (2 * r), (lamR t * energy g.1 * Real.cosh (u / 2) -
          (3 / 2) * energy g.1 * (1 / Real.sinh u)) := by
      apply setIntegral_mono_on hI (hA.sub hB) measurableSet_Ioc
      intro u hu
      exact half_majorant_t g t r a u ht0 htr hw hu.1
    _ = _ := by
      rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
        integral_cosh_half r (2 * r) (by linarith),
        integral_inv_sinh_Ioc r (2 * r) hr0 (by linarith)]
      have h2 : 2 * r / 2 = r := by ring
      rw [h2]
      ring

theorem tail_integral_eq_t (g : WeilCompactSmoothGV1) (t r a : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) :
    (∫ u in Ioi (2 * r), budgetIntegrand g t u) = -energy g.1 * cothTail (2 * r) := by
  rw [← tail_eq g r a hr0 hw]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  unfold budgetIntegrand momentLog
  rw [autocorrelation_zero_of_halfWidth g r a u hw hu]
  simp

/-- **Archimedean budget with a free threshold.** -/
theorem arch_threshold_budget (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t)
    (htr : t ≤ r) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((t / 2) * Real.exp (t / 2)
        + lamR t * (2 * Real.sinh r + 2 * Real.sinh (r / 2) - 8 * Real.sinh (t / 2))
        - 2 * cothTail t + cothTail r / 2 + cothTail (2 * r) / 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le ht0 htr
  have hF := budgetIntegrand_integrableOn g t
  have hs1 : (∫ u in Ioi (0 : ℝ), budgetIntegrand g t u) =
      (∫ u in Ioc (0 : ℝ) t, budgetIntegrand g t u) + ∫ u in Ioi t, budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ht0.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => hu.1))
        (hF.mono_set (fun u hu => lt_trans ht0 hu))]
  have hs2 : (∫ u in Ioi t, budgetIntegrand g t u) =
      (∫ u in Ioc t r, budgetIntegrand g t u) + ∫ u in Ioi r, budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htr,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans ht0 hu.1))
        (hF.mono_set (fun u hu => lt_trans hr0 hu))]
  have hs3 : (∫ u in Ioi r, budgetIntegrand g t u) =
      (∫ u in Ioc r (2 * r), budgetIntegrand g t u) +
        ∫ u in Ioi (2 * r), budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : r ≤ 2 * r),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans hr0 hu.1))
        (hF.mono_set (fun u hu => by
          change 2 * r < u at hu; change (0 : ℝ) < u; linarith))]
  rw [arch_eq_budget_integral g t hm, hs1, hs2, hs3, tail_integral_eq_t g t r a hr0 hw]
  have hi := inner_integral_le g t ht0
  have hf := full_integral_le_t g t r ht0 htr
  have hh := half_integral_le_t g t r a ht0 htr hw
  nlinarith

/-- **Threshold diagonal.**  Below `log 2`, `Re RHS(A) ≤ thrGain t r · E`. -/
theorem threshold_diagonal (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t) (htr : t ≤ r)
    (hlog : 2 * r < Real.log 2) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ thrGain t r * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := arch_threshold_budget g t r a ht0 htr hw hm
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  have heq : thrGain t r * energy g.1 = diagonalKappaV21 * energy g.1 +
      energy g.1 * ((t / 2) * Real.exp (t / 2)
        + lamR t * (2 * Real.sinh r + 2 * Real.sinh (r / 2) - 8 * Real.sinh (t / 2))
        - 2 * cothTail t + cothTail r / 2 + cothTail (2 * r) / 2) := by
    unfold thrGain; ring
  rw [heq]
  linarith

end AEGIS.RHThresholdGainV13

#print axioms AEGIS.RHThresholdGainV13.arch_threshold_budget
#print axioms AEGIS.RHThresholdGainV13.threshold_diagonal
