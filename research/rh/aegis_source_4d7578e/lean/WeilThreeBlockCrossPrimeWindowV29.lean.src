import WeilThreeBlockCrossPrimeV28
import Mathlib.Tactic

/-!
AEGIS Ω — translated three-block prime window isolation V2.9.

Using the exact V2.8 transport and the already kernel-verified
  exp(1/32) < 65/63,
this module proves that the translated mixed correlations, whose total support-difference window has width 1/16 (radius 1/32), can hit
reciprocal positive integers only at:
* m = 2 for adjacent blocks;
* m = 4 for the two-step outer blocks.

All positive-integer samples vanish.  No prime-sum evaluation, Archimedean
cross bound, global Weil positivity, or RH conclusion is asserted here.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilThreeBlockCrossPrimeWindowV29

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilThreeBlockCrossPrimeV28

private theorem nat_eq_two_of_log_window_v29
    {m : ℕ} (hm : 0 < m)
    (hwin :
      |Real.log (m : ℝ) - Real.log 2| ≤ (1 / 32 : ℝ)) :
    m = 2 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have habs := (abs_le.mp hwin)
  have hup_log :
      Real.log (m : ℝ) ≤ Real.log 2 + (1 / 32 : ℝ) := by
    linarith [habs.2]
  have hlo_log :
      Real.log 2 - (1 / 32 : ℝ) ≤ Real.log (m : ℝ) := by
    linarith [habs.1]
  have hup := Real.exp_le_exp.mpr hup_log
  have hlo := Real.exp_le_exp.mpr hlo_log
  have hlog2 : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num)
  rw [Real.exp_add, hlog2] at hup
  rw [sub_eq_add_neg, Real.exp_add, hlog2] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have hlt3r : (m : ℝ) < 3 := by
    nlinarith [exp_one_div_32_lt]
  have hgt1r : (1 : ℝ) < (m : ℝ) := by
    nlinarith [exp_neg_one_div_32_gt]
  have hlt3 : m < 3 := by exact_mod_cast hlt3r
  have hgt1 : 1 < m := by exact_mod_cast hgt1r
  omega

private theorem nat_eq_four_of_log_window_v29
    {m : ℕ} (hm : 0 < m)
    (hwin :
      |Real.log (m : ℝ) - Real.log 4| ≤ (1 / 32 : ℝ)) :
    m = 4 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have habs := (abs_le.mp hwin)
  have hup_log :
      Real.log (m : ℝ) ≤ Real.log 4 + (1 / 32 : ℝ) := by
    linarith [habs.2]
  have hlo_log :
      Real.log 4 - (1 / 32 : ℝ) ≤ Real.log (m : ℝ) := by
    linarith [habs.1]
  have hup := Real.exp_le_exp.mpr hup_log
  have hlo := Real.exp_le_exp.mpr hlo_log
  have hlog4 : Real.exp (Real.log 4) = (4 : ℝ) :=
    Real.exp_log (by norm_num)
  rw [Real.exp_add, hlog4] at hup
  rw [sub_eq_add_neg, Real.exp_add, hlog4] at hlo
  rw [Real.exp_log hmpos] at hup hlo
  have hlt5r : (m : ℝ) < 5 := by
    nlinarith [exp_one_div_32_lt]
  have hgt3r : (3 : ℝ) < (m : ℝ) := by
    nlinarith [exp_neg_one_div_32_gt]
  have hlt5 : m < 5 := by exact_mod_cast hlt5r
  have hgt3 : 3 < m := by exact_mod_cast hgt3r
  omega

private theorem log_four_eq_two_log_two_v29 :
    Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num

/-- Every positive-integer sample of the adjacent mixed correlation is outside
its translated support window. -/
theorem adjacent_mixed_nat_zero_v29
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (m : ℕ) (hm : 0 < m) :
    mixed (gMinus g) (gZero g) (m : ℝ) = 0 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg hm1
  have hL : (1 / 32 : ℝ) < Real.log 2 := by
    linarith [log_two_lower]
  have harg : (0 : ℝ) < Real.log (m : ℝ) + Real.log 2 := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hfar :
      (1 / 32 : ℝ) <
        |Real.log (m : ℝ) + 0 - (-Real.log 2)| := by
    rw [show Real.log (m : ℝ) + 0 - (-Real.log 2) =
        Real.log (m : ℝ) + Real.log 2 by ring,
      abs_of_pos harg]
    linarith
  have hz :=
    mixed_translate_zero_of_width_v28
      g a (-Real.log 2) 0 (Real.log (m : ℝ)) hw hfar
  have hexp : Real.exp (Real.log (m : ℝ)) = (m : ℝ) :=
    Real.exp_log (by exact_mod_cast hm)
  simpa [gMinus, gZero, hexp] using hz

/-- Except for m=2, every reciprocal positive-integer sample of the adjacent
mixed correlation is outside the translated support window. -/
theorem adjacent_mixed_inv_nat_zero_v29
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (m : ℕ) (hm : 0 < m) (hne : m ≠ 2) :
    mixed (gMinus g) (gZero g) ((m : ℝ)⁻¹) = 0 := by
  have hfar0 :
      (1 / 32 : ℝ) <
        |Real.log (m : ℝ) - Real.log 2| := by
    by_contra hnot
    have hle :
        |Real.log (m : ℝ) - Real.log 2| ≤ (1 / 32 : ℝ) :=
      le_of_not_gt hnot
    exact hne (nat_eq_two_of_log_window_v29 hm hle)
  have harg_eq :
      -Real.log (m : ℝ) + 0 - (-Real.log 2) =
        -(Real.log (m : ℝ) - Real.log 2) := by
    ring
  have hfar :
      (1 / 32 : ℝ) <
        |-Real.log (m : ℝ) + 0 - (-Real.log 2)| := by
    rw [harg_eq, abs_neg]
    exact hfar0
  have hz :=
    mixed_translate_zero_of_width_v28
      g a (-Real.log 2) 0 (-Real.log (m : ℝ)) hw hfar
  have hexp :
      Real.exp (-Real.log (m : ℝ)) = ((m : ℝ)⁻¹) := by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)]
  simpa [gMinus, gZero, hexp] using hz

/-- Every positive-integer sample of the outer mixed correlation is outside
its translated support window. -/
theorem outer_mixed_nat_zero_v29
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (m : ℕ) (hm : 0 < m) :
    mixed (gMinus g) (gPlus g) (m : ℝ) = 0 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg hm1
  have hL : (1 / 32 : ℝ) < Real.log 2 := by
    linarith [log_two_lower]
  have harg : (0 : ℝ) <
      Real.log (m : ℝ) + Real.log 2 - (-Real.log 2) := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hfar :
      (1 / 32 : ℝ) <
        |Real.log (m : ℝ) + Real.log 2 - (-Real.log 2)| := by
    rw [abs_of_pos harg]
    linarith
  have hz :=
    mixed_translate_zero_of_width_v28
      g a (-Real.log 2) (Real.log 2) (Real.log (m : ℝ)) hw hfar
  have hexp : Real.exp (Real.log (m : ℝ)) = (m : ℝ) :=
    Real.exp_log (by exact_mod_cast hm)
  simpa [gMinus, gPlus, hexp] using hz

/-- Except for m=4, every reciprocal positive-integer sample of the outer
mixed correlation is outside the translated support window. -/
theorem outer_mixed_inv_nat_zero_v29
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (m : ℕ) (hm : 0 < m) (hne : m ≠ 4) :
    mixed (gMinus g) (gPlus g) ((m : ℝ)⁻¹) = 0 := by
  have hfar0 :
      (1 / 32 : ℝ) <
        |Real.log (m : ℝ) - Real.log 4| := by
    by_contra hnot
    have hle :
        |Real.log (m : ℝ) - Real.log 4| ≤ (1 / 32 : ℝ) :=
      le_of_not_gt hnot
    exact hne (nat_eq_four_of_log_window_v29 hm hle)
  have hlog4 := log_four_eq_two_log_two_v29
  have harg_eq :
      -Real.log (m : ℝ) + Real.log 2 - (-Real.log 2) =
        -(Real.log (m : ℝ) - Real.log 4) := by
    rw [hlog4]
    ring
  have hfar :
      (1 / 32 : ℝ) <
        |-Real.log (m : ℝ) + Real.log 2 - (-Real.log 2)| := by
    rw [harg_eq, abs_neg]
    exact hfar0
  have hz :=
    mixed_translate_zero_of_width_v28
      g a (-Real.log 2) (Real.log 2) (-Real.log (m : ℝ)) hw hfar
  have hexp :
      Real.exp (-Real.log (m : ℝ)) = ((m : ℝ)⁻¹) := by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)]
  simpa [gMinus, gPlus, hexp] using hz

end AEGIS.WeilThreeBlockCrossPrimeWindowV29

#print axioms AEGIS.WeilThreeBlockCrossPrimeWindowV29.adjacent_mixed_nat_zero_v29
#print axioms AEGIS.WeilThreeBlockCrossPrimeWindowV29.adjacent_mixed_inv_nat_zero_v29
#print axioms AEGIS.WeilThreeBlockCrossPrimeWindowV29.outer_mixed_nat_zero_v29
#print axioms AEGIS.WeilThreeBlockCrossPrimeWindowV29.outer_mixed_inv_nat_zero_v29
