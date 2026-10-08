import WeilThreeBlockCrossPrimeWindowV29

/-!
Candidate source, not yet kernel replayed.
Evaluates the actual prime sums after V2.9 window isolation.
No Archimedean bound or RH theorem is assumed or asserted here.
-/
open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilThreeBlockPrimeEvaluationV30
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilThreeBlockCrossPrimeWindowV29

theorem adjacent_prime_sum_single
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (gMinus g) (gZero g)) =
      WeilPrimeTermV1 (mixed (gMinus g) (gZero g)) 1 := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single 1
  intro n hn
  have hp := adjacent_mixed_nat_zero_v29 g a hw (n + 1) (by omega)
  have hi := adjacent_mixed_inv_nat_zero_v29 g a hw (n + 1)
    (by omega) (by omega)
  simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

theorem outer_prime_sum_single
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (gMinus g) (gPlus g)) =
      WeilPrimeTermV1 (mixed (gMinus g) (gPlus g)) 3 := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single 3
  intro n hn
  have hp := outer_mixed_nat_zero_v29 g a hw (n + 1) (by omega)
  have hi := outer_mixed_inv_nat_zero_v29 g a hw (n + 1)
    (by omega) (by omega)
  simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

theorem exp_log_two_half : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  have he : Real.exp (Real.log 2 / 2) ^ 2 = (2 : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    rw [show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring]
    exact Real.exp_log (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.exp_pos (Real.log 2 / 2)
  have hsp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem adjacent_mixed_reciprocal_center (g : WeilCompactSmoothGV1) :
    mixed (gMinus g) (gZero g) ((2 : ℝ)⁻¹) =
      (Real.sqrt 2 : ℂ) * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g (-Real.log 2) 0
  have he : Real.exp ((-Real.log 2 - 0) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [show (-Real.log 2 - 0) / 2 = -(Real.log 2 / 2) by ring,
      Real.exp_neg, exp_log_two_half]
  have hx : Real.exp (-Real.log 2 - 0) = (2 : ℝ)⁻¹ := by
    rw [sub_zero, Real.exp_neg, Real.exp_log (by norm_num)]
  change (Real.exp ((-Real.log 2 - 0) / 2) : ℂ) *
    mixed (gMinus g) (gZero g) (Real.exp (-Real.log 2 - 0)) = _ at h
  rw [he, hx, Complex.ofReal_inv] at h
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  calc
    mixed (gMinus g) (gZero g) ((2 : ℝ)⁻¹) =
        (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹ *
          mixed (gMinus g) (gZero g) ((2 : ℝ)⁻¹)) := by field_simp
    _ = (Real.sqrt 2 : ℂ) * (energy g.1 : ℂ) := by rw [h]

theorem outer_mixed_reciprocal_center (g : WeilCompactSmoothGV1) :
    mixed (gMinus g) (gPlus g) ((4 : ℝ)⁻¹) =
      2 * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g (-Real.log 2) (Real.log 2)
  have he : Real.exp ((-Real.log 2 - Real.log 2) / 2) = (2 : ℝ)⁻¹ := by
    rw [show (-Real.log 2 - Real.log 2) / 2 = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num)]
  have hx : Real.exp (-Real.log 2 - Real.log 2) = (4 : ℝ)⁻¹ := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  change (Real.exp ((-Real.log 2 - Real.log 2) / 2) : ℂ) *
    mixed (gMinus g) (gPlus g) (Real.exp (-Real.log 2 - Real.log 2)) = _ at h
  rw [he, hx] at h
  simp only [Complex.ofReal_inv, Complex.ofReal_ofNat] at h
  calc
    mixed (gMinus g) (gPlus g) ((4 : ℝ)⁻¹) =
        (2 : ℂ) * ((2 : ℂ)⁻¹ * mixed (gMinus g) (gPlus g) ((4 : ℝ)⁻¹)) := by ring
    _ = 2 * (energy g.1 : ℂ) := by rw [h]

theorem adjacent_prime_sum_exact
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (gMinus g) (gZero g)) =
      ((Real.log 2 / Real.sqrt 2 * energy g.1 : ℝ) : ℂ) := by
  rw [adjacent_prime_sum_single g a hw]
  have hp : mixed (gMinus g) (gZero g) (2 : ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using adjacent_mixed_nat_zero_v29 g a hw 2 (by norm_num)
  have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  change (ArithmeticFunction.vonMangoldt 2 : ℂ) *
    (mixed (gMinus g) (gZero g) (2 : ℝ) + (1 / (2 : ℂ)) *
      mixed (gMinus g) (gZero g) ((2 : ℝ)⁻¹)) = _
  rw [hp, adjacent_mixed_reciprocal_center, hv]
  push_cast
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hscalar : (1 / (2 : ℂ)) * (Real.sqrt 2 : ℂ) =
      1 / (Real.sqrt 2 : ℂ) := by
    field_simp
    linear_combination hs
  calc
    (Real.log 2 : ℂ) * (0 + 1 / 2 *
        ((Real.sqrt 2 : ℂ) * (energy g.1 : ℂ))) =
      (Real.log 2 : ℂ) * ((1 / 2 * (Real.sqrt 2 : ℂ)) *
        (energy g.1 : ℂ)) := by ring
    _ = _ := by rw [hscalar]; ring

theorem outer_prime_sum_exact
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (gMinus g) (gPlus g)) =
      ((Real.log 2 / 2 * energy g.1 : ℝ) : ℂ) := by
  rw [outer_prime_sum_single g a hw]
  have hp : mixed (gMinus g) (gPlus g) (4 : ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using outer_mixed_nat_zero_v29 g a hw 4 (by norm_num)
  have hv : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
    exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  change (ArithmeticFunction.vonMangoldt 4 : ℂ) *
    (mixed (gMinus g) (gPlus g) (4 : ℝ) + (1 / (4 : ℂ)) *
      mixed (gMinus g) (gPlus g) ((4 : ℝ)⁻¹)) = _
  rw [hp, outer_mixed_reciprocal_center, hv]
  push_cast
  ring

theorem adjacent_mixed_shift_eq
    (g : WeilCompactSmoothGV1) (x : ℝ) (hx : 0 < x) :
    mixed (gZero g) (gPlus g) x = mixed (gMinus g) (gZero g) x := by
  have h1 := exp_half_mul_mixed_translate_v28 g 0 (Real.log 2) (Real.log x)
  have h2 := exp_half_mul_mixed_translate_v28 g (-Real.log 2) 0 (Real.log x)
  have he : (Real.exp (Real.log x / 2) : ℂ) ≠ 0 := by simp
  apply mul_left_cancel₀ he
  have h1' : (Real.exp (Real.log x / 2) : ℂ) *
      mixed (gZero g) (gPlus g) x =
      AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g (Real.log x + Real.log 2) := by
    simpa [gZero, gPlus, Real.exp_log hx] using h1
  have h2' : (Real.exp (Real.log x / 2) : ℂ) *
      mixed (gMinus g) (gZero g) x =
      AEGIS.WeilWidthArchCorrelationV25.logCorrelationV25 g (Real.log x + Real.log 2) := by
    simpa [gMinus, gZero, Real.exp_log hx, sub_neg_eq_add] using h2
  exact h1'.trans h2'.symm

theorem right_adjacent_prime_sum_exact
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (mixed (gZero g) (gPlus g)) =
      ((Real.log 2 / Real.sqrt 2 * energy g.1 : ℝ) : ℂ) := by
  calc
    WeilPrimeSumV1 (mixed (gZero g) (gPlus g)) =
        WeilPrimeSumV1 (mixed (gMinus g) (gZero g)) := by
      unfold WeilPrimeSumV1
      apply tsum_congr
      intro n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      simp only [WeilPrimeTermV1,
        adjacent_mixed_shift_eq g _ hn,
        adjacent_mixed_shift_eq g _ (inv_pos.mpr hn)]
    _ = _ := adjacent_prime_sum_exact g a hw

end AEGIS.WeilThreeBlockPrimeEvaluationV30

#print axioms AEGIS.WeilThreeBlockPrimeEvaluationV30.adjacent_prime_sum_exact
#print axioms AEGIS.WeilThreeBlockPrimeEvaluationV30.outer_prime_sum_exact
#print axioms AEGIS.WeilThreeBlockPrimeEvaluationV30.right_adjacent_prime_sum_exact
