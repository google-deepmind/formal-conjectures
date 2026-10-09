import WeilSeparatedArchBridgeV31
import Mathlib.Tactic

/-!
AEGIS Omega -- missing dyadic n=8 entry, source candidate V3.
Base: db97cff9d4b918b727033c08cbb8bf37b2981039.
The existing packet, mixed correlation, von Mangoldt sum and B are reused.
All claims here require pinned Lean compilation and an actual axiom audit.
No global sign, RH, runtime/admission or physical claim is made.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockPrimeEightV3
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilThreeBlockPrimeEvaluationV30
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilSeparatedArchBridgeV31

/-- The positive-source carrier makes every nonpositive mixed sample zero. -/
theorem mixed_zero_of_nonpos_v3 (p q : WeilCompactSmoothGV1)
    {x : ℝ} (hx : x ≤ 0) : mixed p q x = 0 := by
  unfold mixed
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have hz := packet_eq_zero_of_nonpos p
    (mul_nonpos_of_nonpos_of_nonneg hx hy.le)
  rw [hz, zero_mul]

/-- Equality of gaps gives equality of the complete mixed functions,
including x <= 0, not just selected prime samples. -/
theorem mixed_translate_eq_of_gap_v3 (g : WeilCompactSmoothGV1)
    (d1 d2 e1 e2 : ℝ) (hgap : d2 - d1 = e2 - e1) :
    mixed (translatePacket g d1) (translatePacket g d2) =
      mixed (translatePacket g e1) (translatePacket g e2) := by
  funext x
  by_cases hx : 0 < x
  · have h1 := exp_half_mul_mixed_translate_v28 g d1 d2 (Real.log x)
    have h2 := exp_half_mul_mixed_translate_v28 g e1 e2 (Real.log x)
    rw [Real.exp_log hx] at h1 h2
    have ha : Real.log x + d2 - d1 = Real.log x + e2 - e1 := by linarith
    rw [ha] at h1
    have he : (Real.exp (Real.log x / 2) : ℂ) ≠ 0 := by simp
    exact mul_left_cancel₀ he (h1.trans h2.symm)
  · rw [mixed_zero_of_nonpos_v3 _ _ (le_of_not_gt hx),
        mixed_zero_of_nonpos_v3 _ _ (le_of_not_gt hx)]

theorem B_translate_eq_of_gap_v3 (g : WeilCompactSmoothGV1)
    (d1 d2 e1 e2 : ℝ) (hgap : d2 - d1 = e2 - e1) :
    B (translatePacket g d1) (translatePacket g d2) =
      B (translatePacket g e1) (translatePacket g e2) := by
  unfold B
  rw [mixed_translate_eq_of_gap_v3 g d1 d2 e1 e2 hgap]

theorem log_eight_eq_v3 : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  norm_num

/-- All positive integers in the closed radius-1/32 log-window are 8.
The proof encloses m between 8*(31/32)>7 and 8*(32/31)<9. -/
theorem nat_eq_eight_of_log_window_v3 {m : ℕ} (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - Real.log 8| ≤ (1 / 32 : ℝ)) : m = 8 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  have hup := Real.exp_le_exp.mpr
    (show Real.log (m : ℝ) ≤ Real.log 8 + 1 / 32 by linarith)
  have hlo := Real.exp_le_exp.mpr
    (show Real.log 8 - 1 / 32 ≤ Real.log (m : ℝ) by linarith)
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8),
      Real.exp_log hmpos] at hup
  rw [sub_eq_add_neg, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 8), Real.exp_log hmpos] at hlo
  have he : Real.exp (1 / 32 : ℝ) < (32 / 31 : ℝ) := by
    calc
      _ < 1 / (1 - (1 / 32 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have hn := Real.add_one_le_exp (-(1 / 32 : ℝ))
  have hlt9r : (m : ℝ) < 9 := by nlinarith
  have hgt7r : (7 : ℝ) < (m : ℝ) := by nlinarith
  have hlt9 : m < 9 := by exact_mod_cast hlt9r
  have hgt7 : 7 < m := by exact_mod_cast hgt7r
  omega

theorem farthest_mixed_nat_zero_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (m : ℕ) (hm : 0 < m) :
    mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) (m : ℝ) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hlogm := Real.log_nonneg hm1
  have ha : 0 < Real.log (m : ℝ) + 3 * Real.log 2 - 0 := by
    linarith [log_two_lower]
  have hfar : (1 / 32 : ℝ) < |Real.log (m : ℝ) + 3 * Real.log 2 - 0| := by
    rw [abs_of_pos ha]
    linarith [log_two_lower]
  have hz := mixed_translate_zero_of_width_v28 g a 0 (3 * Real.log 2)
    (Real.log (m : ℝ)) hw hfar
  simpa only [Real.exp_log hmpos] using hz

theorem farthest_mixed_inv_nat_zero_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (m : ℕ) (hm : 0 < m) (hne : m ≠ 8) :
    mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) ((m : ℝ)⁻¹) = 0 := by
  have hfar0 : (1 / 32 : ℝ) < |Real.log (m : ℝ) - Real.log 8| := by
    by_contra h
    exact hne (nat_eq_eight_of_log_window_v3 hm (le_of_not_gt h))
  have ha : -Real.log (m : ℝ) + 3 * Real.log 2 - 0 =
      -(Real.log (m : ℝ) - Real.log 8) := by rw [log_eight_eq_v3]; ring
  have hfar : (1 / 32 : ℝ) < |-Real.log (m : ℝ) + 3 * Real.log 2 - 0| := by
    rw [ha, abs_neg]
    exact hfar0
  have hz := mixed_translate_zero_of_width_v28 g a 0 (3 * Real.log 2)
    (-Real.log (m : ℝ)) hw hfar
  have he : Real.exp (-Real.log (m : ℝ)) = (m : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)]
  simpa only [he] using hz

theorem farthest_prime_sum_single_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2))) =
      WeilPrimeTermV1 (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2))) 7 := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single 7
  intro n hn
  have hp := farthest_mixed_nat_zero_v3 g a hw (n + 1) (by omega)
  have hi := farthest_mixed_inv_nat_zero_v3 g a hw (n + 1) (by omega) (by omega)
  simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

theorem exp_three_log_two_half_v3 :
    Real.exp (3 * Real.log 2 / 2) = 2 * Real.sqrt 2 := by
  rw [show 3 * Real.log 2 / 2 = Real.log 2 + Real.log 2 / 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), exp_log_two_half]

theorem farthest_mixed_reciprocal_center_v3 (g : WeilCompactSmoothGV1) :
    mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) ((8 : ℝ)⁻¹) =
      (2 : ℂ) * (Real.sqrt 2 : ℂ) * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g 0 (3 * Real.log 2)
  have he : Real.exp ((0 - 3 * Real.log 2) / 2) = (2 * Real.sqrt 2)⁻¹ := by
    rw [show (0 - 3 * Real.log 2) / 2 = -(3 * Real.log 2 / 2) by ring,
        Real.exp_neg, exp_three_log_two_half_v3]
  have hx : Real.exp (0 - 3 * Real.log 2) = (8 : ℝ)⁻¹ := by
    rw [zero_sub, Real.exp_neg, ← log_eight_eq_v3,
        Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  rw [he, hx, Complex.ofReal_inv, Complex.ofReal_mul] at h
  simp only [Complex.ofReal_ofNat] at h
  let s : ℂ := (2 : ℂ) * (Real.sqrt 2 : ℂ)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))
  change s⁻¹ * mixed (translatePacket g 0)
    (translatePacket g (3 * Real.log 2)) ((8 : ℝ)⁻¹) = (energy g.1 : ℂ) at h
  calc
    _ = s * (s⁻¹ * mixed (translatePacket g 0)
        (translatePacket g (3 * Real.log 2)) ((8 : ℝ)⁻¹)) := by field_simp [hs]
    _ = s * (energy g.1 : ℂ) := by rw [h]
    _ = _ := rfl

/-- Lambda(8) is log(2), NOT log(8). The coefficient is
log(2)*sqrt(2)/4 = log(2)/sqrt(8). -/
theorem farthest_prime_sum_exact_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2))) =
      ((Real.log 2 * Real.sqrt 2 / 4 * energy g.1 : ℝ) : ℂ) := by
  rw [farthest_prime_sum_single_v3 g a hw]
  have hp8 :
      mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) (8 : ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using
      farthest_mixed_nat_zero_v3 g a hw 8 (by norm_num)
  have hv : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  change (ArithmeticFunction.vonMangoldt 8 : ℂ) *
    (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) (8 : ℝ) +
      (1 / (8 : ℂ)) * mixed (translatePacket g 0)
        (translatePacket g (3 * Real.log 2)) ((8 : ℝ)⁻¹)) = _
  rw [hp8, farthest_mixed_reciprocal_center_v3 g, hv]
  push_cast
  ring

theorem farthest_prime_scalar_lt_quarter_v3 :
    Real.log 2 * Real.sqrt 2 / 4 < (1 / 4 : ℝ) := by
  have hs : Real.sqrt 2 < (10 / 7 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hp := mul_lt_mul_of_pos_right log_two_upper
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  nlinarith

/-- Complete missing actual-B estimate. Width and repository moments are
inputs; the prime value, zero centre and Archimedean estimate are derived. -/
theorem farthest_B_norm_bound_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g) :
    ‖B (translatePacket g 0) (translatePacket g (3 * Real.log 2))‖ ≤
      (13 / 50 : ℝ) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hc : 0 ≤ Real.log 2 * Real.sqrt 2 / 4 :=
    div_nonneg (mul_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _))
      (by norm_num)
  have hp : ‖WeilPrimeSumV1
      (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)))‖ =
      (Real.log 2 * Real.sqrt 2 / 4) * energy g.1 := by
    rw [farthest_prime_sum_exact_v3 g a hw, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hc hE)]
  have ha := translated_arch_norm_bound g a 0 (3 * Real.log 2) hw hm
    (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hz : mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)) 1 = 0 := by
    simpa using farthest_mixed_nat_zero_v3 g a hw 1 (by norm_num)
  unfold B WeilExplicitRightSideV1
  rw [hz, mul_zero, add_zero]
  calc
    _ ≤ ‖WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (3 * Real.log 2)))‖ +
        ‖WeilArchimedeanIntegralV1 (mixed (translatePacket g 0)
          (translatePacket g (3 * Real.log 2)))‖ := norm_add_le _ _
    _ ≤ (Real.log 2 * Real.sqrt 2 / 4) * energy g.1 + (1 / 100 : ℝ) * energy g.1 := by
      rw [hp]
      exact add_le_add le_rfl ha
    _ ≤ (13 / 50 : ℝ) * energy g.1 := by
      nlinarith [mul_le_mul_of_nonneg_right farthest_prime_scalar_lt_quarter_v3.le hE]

end AEGIS.RHFourBlockPrimeEightV3

#print axioms AEGIS.RHFourBlockPrimeEightV3.mixed_zero_of_nonpos_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.mixed_translate_eq_of_gap_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.B_translate_eq_of_gap_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.log_eight_eq_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.nat_eq_eight_of_log_window_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_mixed_nat_zero_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_mixed_inv_nat_zero_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_prime_sum_single_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.exp_three_log_two_half_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_mixed_reciprocal_center_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_prime_sum_exact_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_prime_scalar_lt_quarter_v3
#print axioms AEGIS.RHFourBlockPrimeEightV3.farthest_B_norm_bound_v3
