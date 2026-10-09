import RHThresholdGainV13
import Mathlib.Tactic

/-!
AEGIS Ω — the threshold gain with the `½`-bonus on the lower-bound pieces, V13.

Every majorant on a piece where the kernel is `≤ 0` (`RHMomentGainV13.middle_majorant`,
`RHThresholdGainV13.half_majorant_t`) drops a term `−c·E·(e^{u/2} − 1)/sinh u`, using
only that it is `≤ 0`.  For `0 < u ≤ 1` it is in fact `≤ −c·E/2`:

  (e^{u/2} − 1)/sinh u ≥ ½   ⇔   (x² − 2x − 1)(x − 1)² ≤ 0,   x = e^{u/2} ≤ 2.

Keeping it on `(t, r]` (full cap, `c = 1`) and `(r, 2r]` (half-cap, `c = ½`) gives

  Re RHS(A) ≤ bonusGain t r · E,   bonusGain t r = thrGain t r − (r − t)/2 − r/4,

for `0 < t ≤ r`, `2r ≤ 1`, `2r < log 2`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBonusGainV13
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
open AEGIS.RHThresholdGainV13

/-- The bonus gain: `thrGain` improved by the `½`-bonus. -/
def bonusGain (t r : ℝ) : ℝ := thrGain t r - (r - t) / 2 - r / 4

/-- `(e^{u/2} − 1)/sinh u ≥ ½` for `0 < u ≤ 1`. -/
theorem half_le_bonus (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (1 : ℝ) / 2 ≤ (Real.exp (u / 2) - 1) / Real.sinh u := by
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  rw [le_div_iff₀ hsu]
  set x := Real.exp (u / 2) with hx
  have hx1 : 1 ≤ x := Real.one_le_exp (by linarith)
  have hxx : x * x = Real.exp u := by rw [hx, ← Real.exp_add]; ring_nf
  have hx2 : x ≤ 2 := by
    have he : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr hu1
    have h1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    nlinarith
  have hxinv : x * Real.exp (-(u / 2)) = 1 := by rw [hx, ← Real.exp_add]; simp
  have hyy : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have hsinh : Real.sinh u = (x * x - Real.exp (-(u / 2)) * Real.exp (-(u / 2))) / 2 := by
    rw [Real.sinh_eq, hxx, hyy]
  rw [hsinh]
  set y := Real.exp (-(u / 2)) with hy
  have hy0 : 0 < y := Real.exp_pos _
  -- multiply through by x² (with x·y = 1)
  have key : (x * x - y * y) * x * x = x ^ 4 - 1 := by
    have : (x * y) ^ 2 = 1 := by rw [hxinv]; norm_num
    nlinarith [this]
  have hx0 : 0 < x := by linarith
  have hpoly : x ^ 4 - 1 ≤ 4 * x ^ 2 * (x - 1) := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by nlinarith : (0 : ℝ) ≤ 1 + 2 * x - x ^ 2)]
  have hxx0 : 0 < x * x := by positivity
  nlinarith [key, hpoly, hxx0]

/-- Full-cap majorant with the bonus, `t ≤ u ≤ 1`. -/
theorem full_majorant_bonus (g : WeilCompactSmoothGV1) (t u : ℝ) (ht0 : 0 < t) (htu : t ≤ u)
    (hu1 : u ≤ 1) :
    budgetIntegrand g t u ≤
      2 * lamR t * energy g.1 * Real.cosh (u / 2) - 2 * energy g.1 * (1 / Real.sinh u)
        - energy g.1 / 2 := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := lt_of_lt_of_le ht0 htu
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos t u ht0 htu
  have hnorm := autocorrelation_exp_norm_le_v26 g u
  have hre : -‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
      (WeilAutocorrelationV1 g (Real.exp u)).re :=
    le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
  have hexp : Real.exp u * Real.exp (-u / 2) = Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hh : -(Real.exp (u / 2) * energy g.1) ≤
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re := by
    have hpos := Real.exp_pos u
    have := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hnorm) hre) hpos.le
    rw [mul_neg, ← mul_assoc, hexp] at this
    exact this
  have h1 := mul_le_mul_of_nonpos_right hh hk
  have h4 := exp_half_mul u
  have hge : energy g.1 / 2 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    have := mul_le_mul_of_nonneg_left (half_le_bonus u hu0 hu1) hE
    linarith
  have h2 : -(Real.exp (u / 2) * energy g.1) *
        (1 / Real.sinh u - lamR t * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      lamR t * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) -
        2 * energy g.1 * (1 / Real.sinh u) -
        energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  linarith

/-- Half-cap majorant with the bonus, `r < u ≤ 1`. -/
theorem half_majorant_bonus (g : WeilCompactSmoothGV1) (t r a u : ℝ) (ht0 : 0 < t)
    (htr : t ≤ r) (hw : HalfWidthAt g r a) (hru : r < u) (hu1 : u ≤ 1) :
    budgetIntegrand g t u ≤
      lamR t * energy g.1 * Real.cosh (u / 2) - (3 / 2) * energy g.1 * (1 / Real.sinh u)
        - energy g.1 / 4 := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := by linarith
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos t u ht0 (by linarith)
  have hh := half_cap_exp_re_lower g r a u hw hru
  have h1 := mul_le_mul_of_nonpos_right hh hk
  have h4 := exp_half_mul u
  have hge : energy g.1 / 2 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    have := mul_le_mul_of_nonneg_left (half_le_bonus u hu0 hu1) hE
    linarith
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

theorem full_integral_le_bonus (g : WeilCompactSmoothGV1) (t r : ℝ) (ht0 : 0 < t)
    (htr : t ≤ r) (hr1 : r ≤ 1) :
    (∫ u in Ioc t r, budgetIntegrand g t u) ≤
      4 * lamR t * energy g.1 * (Real.sinh (r / 2) - Real.sinh (t / 2)) -
        2 * energy g.1 * (cothTail t - cothTail r) - energy g.1 / 2 * (r - t) := by
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc t r) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans ht0 hu.1)
  have hA := (cosh_half_integrableOn t r).const_mul (2 * lamR t * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc t r ht0).const_mul (2 * energy g.1)
  have hC : IntegrableOn (fun _ : ℝ => energy g.1 / 2) (Ioc t r) :=
    continuous_const.integrableOn_Ioc
  have hAB : IntegrableOn (fun u : ℝ => 2 * lamR t * energy g.1 * Real.cosh (u / 2) -
      2 * energy g.1 * (1 / Real.sinh u)) (Ioc t r) := hA.sub hB
  calc
    _ ≤ ∫ u in Ioc t r, (2 * lamR t * energy g.1 * Real.cosh (u / 2) -
          2 * energy g.1 * (1 / Real.sinh u) - energy g.1 / 2) := by
      apply setIntegral_mono_on hI (hAB.sub hC) measurableSet_Ioc
      intro u hu
      exact full_majorant_bonus g t u ht0 hu.1.le (le_trans hu.2 hr1)
    _ = _ := by
      rw [integral_sub hAB hC, integral_sub hA hB, integral_const_mul,
        integral_const_mul, integral_cosh_half t r htr, integral_inv_sinh_Ioc t r ht0 htr,
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le htr]
      ring

theorem half_integral_le_bonus (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t)
    (htr : t ≤ r) (hr1 : 2 * r ≤ 1) (hw : HalfWidthAt g r a) :
    (∫ u in Ioc r (2 * r), budgetIntegrand g t u) ≤
      2 * lamR t * energy g.1 * (Real.sinh r - Real.sinh (r / 2)) -
        (3 / 2) * energy g.1 * (cothTail r - cothTail (2 * r)) - energy g.1 / 4 * r := by
  have hr0 : 0 < r := lt_of_lt_of_le ht0 htr
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc r (2 * r)) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans hr0 hu.1)
  have hA := (cosh_half_integrableOn r (2 * r)).const_mul (lamR t * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc r (2 * r) hr0).const_mul ((3 / 2) * energy g.1)
  have hC : IntegrableOn (fun _ : ℝ => energy g.1 / 4) (Ioc r (2 * r)) :=
    continuous_const.integrableOn_Ioc
  have hAB : IntegrableOn (fun u : ℝ => lamR t * energy g.1 * Real.cosh (u / 2) -
      (3 / 2) * energy g.1 * (1 / Real.sinh u)) (Ioc r (2 * r)) := hA.sub hB
  calc
    _ ≤ ∫ u in Ioc r (2 * r), (lamR t * energy g.1 * Real.cosh (u / 2) -
          (3 / 2) * energy g.1 * (1 / Real.sinh u) - energy g.1 / 4) := by
      apply setIntegral_mono_on hI (hAB.sub hC) measurableSet_Ioc
      intro u hu
      exact half_majorant_bonus g t r a u ht0 htr hw hu.1 (le_trans hu.2 hr1)
    _ = _ := by
      rw [integral_sub hAB hC, integral_sub hA hB, integral_const_mul,
        integral_const_mul, integral_cosh_half r (2 * r) (by linarith),
        integral_inv_sinh_Ioc r (2 * r) hr0 (by linarith), setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le (by linarith : r ≤ 2 * r)]
      have h2 : 2 * r / 2 = r := by ring
      rw [h2]
      ring

/-- **Archimedean budget with the bonus.** -/
theorem arch_bonus_budget (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t)
    (htr : t ≤ r) (hr1 : 2 * r ≤ 1) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * ((t / 2) * Real.exp (t / 2)
        + lamR t * (2 * Real.sinh r + 2 * Real.sinh (r / 2) - 8 * Real.sinh (t / 2))
        - 2 * cothTail t + cothTail r / 2 + cothTail (2 * r) / 2
        - (r - t) / 2 - r / 4) := by
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
  have hf := full_integral_le_bonus g t r ht0 htr (by linarith)
  have hh := half_integral_le_bonus g t r a ht0 htr hr1 hw
  nlinarith

/-- **Bonus diagonal.**  `Re RHS(A) ≤ bonusGain t r · E`. -/
theorem bonus_diagonal (g : WeilCompactSmoothGV1) (t r a : ℝ) (ht0 : 0 < t) (htr : t ≤ r)
    (hr1 : 2 * r ≤ 1) (hlog : 2 * r < Real.log 2) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ bonusGain t r * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := arch_bonus_budget g t r a ht0 htr hr1 hw hm
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  have heq : bonusGain t r * energy g.1 = diagonalKappaV21 * energy g.1 +
      energy g.1 * ((t / 2) * Real.exp (t / 2)
        + lamR t * (2 * Real.sinh r + 2 * Real.sinh (r / 2) - 8 * Real.sinh (t / 2))
        - 2 * cothTail t + cothTail r / 2 + cothTail (2 * r) / 2
        - (r - t) / 2 - r / 4) := by
    unfold bonusGain thrGain; ring
  rw [heq]
  linarith

end AEGIS.RHBonusGainV13

#print axioms AEGIS.RHBonusGainV13.half_le_bonus
#print axioms AEGIS.RHBonusGainV13.arch_bonus_budget
#print axioms AEGIS.RHBonusGainV13.bonus_diagonal
