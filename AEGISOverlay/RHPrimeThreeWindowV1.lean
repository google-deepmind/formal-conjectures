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

import RHDyadicWindowV13
import Mathlib.Tactic

/-!
# Prime-3 translation window for the RH snowflake lane

This overlay generalizes the already audited dyadic cross-term mechanism from
gaps k*log 2 to gaps k*log 3.  At sufficiently narrow half-width, the only
integer in the reciprocal prime window is 3^k, so the actual Riemann-zeta prime
sum is exactly log(3)*3^(-k/2)*E.

No RH or global positivity statement is asserted here.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeThreeWindowV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHDyadicWindowV13

def triadicHalf (k : ℕ) : ℝ :=
  Real.exp (-(k * Real.log 3) / 2)

theorem triadicHalf_pos (k : ℕ) : 0 < triadicHalf k :=
  Real.exp_pos _

theorem log_two_lt_log_three : Real.log 2 < Real.log 3 := by
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

theorem nat_eq_pow_three_of_log_window
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 < r)
    (hr : 2 * r ≤ 1 / (2 * (3 : ℝ) ^ k))
    {m : ℕ} (hm : 0 < m)
    (hw : |Real.log (m : ℝ) - k * Real.log 3| ≤ 2 * r) :
    m = 3 ^ k := by
  have hP : (0 : ℝ) < 3 ^ k := by positivity
  have hP2 : (2 : ℝ) ≤ 3 ^ k := by
    calc
      (2 : ℝ) ≤ 3 := by norm_num
      _ = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  have hlogP : Real.log ((3 : ℝ) ^ k) = k * Real.log 3 := by
    rw [Real.log_pow]
  have hdenpos : 0 < (2 : ℝ) * 3 ^ k := by positivity
  have hsmall : 2 * r * (2 * (3 : ℝ) ^ k) ≤ 1 := by
    exact (le_div_iff₀ hdenpos).mp hr
  have h2r1 : 2 * r < 1 := by
    nlinarith
  have hup : (m : ℝ) ≤ 3 ^ k * Real.exp (2 * r) := by
    have := Real.exp_le_exp.mpr
      (show Real.log (m : ℝ) ≤ Real.log ((3 : ℝ) ^ k) + 2 * r by
        rw [hlogP]
        linarith)
    rwa [Real.exp_add, Real.exp_log hP, Real.exp_log hmpos] at this
  have hlo : 3 ^ k * Real.exp (-(2 * r)) ≤ (m : ℝ) := by
    have := Real.exp_le_exp.mpr
      (show Real.log ((3 : ℝ) ^ k) - 2 * r ≤ Real.log (m : ℝ) by
        rw [hlogP]
        linarith)
    rwa [sub_eq_add_neg, Real.exp_add, Real.exp_log hP, Real.exp_log hmpos] at this
  have hexp_up : Real.exp (2 * r) ≤ 1 / (1 - 2 * r) :=
    Real.exp_bound_div_one_sub_of_interval (by linarith) h2r1
  have hexp_lo : 1 - 2 * r ≤ Real.exp (-(2 * r)) := by
    linarith [Real.add_one_le_exp (-(2 * r))]
  have hlt : (m : ℝ) < 3 ^ k + 1 := by
    calc
      (m : ℝ) ≤ 3 ^ k * Real.exp (2 * r) := hup
      _ ≤ 3 ^ k * (1 / (1 - 2 * r)) :=
        mul_le_mul_of_nonneg_left hexp_up hP.le
      _ < 3 ^ k + 1 := by
        rw [mul_one_div, div_lt_iff₀ (by linarith)]
        nlinarith
  have hgt : (3 : ℝ) ^ k < m + 1 := by
    calc
      (3 : ℝ) ^ k < 3 ^ k * (1 - 2 * r) + 1 := by nlinarith
      _ ≤ 3 ^ k * Real.exp (-(2 * r)) + 1 := by
        linarith [mul_le_mul_of_nonneg_left hexp_lo hP.le]
      _ ≤ m + 1 := by linarith
  have h1 : m < 3 ^ k + 1 := by exact_mod_cast hlt
  have h2 : 3 ^ k < m + 1 := by exact_mod_cast hgt
  omega

theorem gap_mixed_nat_zero_three
    (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr64 : r ≤ 1 / 64) (hw : HalfWidthAt g r a)
    (m : ℕ) (hm : 0 < m) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)) (m : ℝ) = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_nonneg hm1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < Real.log (m : ℝ) + k * Real.log 3 - 0 := by
    nlinarith [log_two_lower, log_two_lt_log_three]
  have hfar : 2 * r < |Real.log (m : ℝ) + k * Real.log 3 - 0| := by
    rw [abs_of_pos hpos]
    nlinarith [log_two_lower, log_two_lt_log_three]
  have hz := mixed_translate_zero_of_halfWidth
    g r a 0 (k * Real.log 3) (Real.log (m : ℝ)) hw hfar
  simpa only [Real.exp_log hmpos] using hz

theorem gap_mixed_inv_nat_zero_three
    (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 * (3 : ℝ) ^ k))
    (hw : HalfWidthAt g r a)
    (m : ℕ) (hm : 0 < m) (hne : m ≠ 3 ^ k) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 3))
      ((m : ℝ)⁻¹) = 0 := by
  have hfar0 : 2 * r < |Real.log (m : ℝ) - k * Real.log 3| := by
    by_contra h
    exact hne
      (nat_eq_pow_three_of_log_window k hk r hr0 hr hm (le_of_not_gt h))
  have ha :
      -Real.log (m : ℝ) + k * Real.log 3 - 0 =
        -(Real.log (m : ℝ) - k * Real.log 3) := by
    ring
  have hfar :
      2 * r < |-Real.log (m : ℝ) + k * Real.log 3 - 0| := by
    rw [ha, abs_neg]
    exact hfar0
  have hz := mixed_translate_zero_of_halfWidth
    g r a 0 (k * Real.log 3) (-Real.log (m : ℝ)) hw hfar
  have he : Real.exp (-Real.log (m : ℝ)) = (m : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)]
  simpa only [he] using hz

theorem gap_prime_sum_single_three
    (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 * (3 : ℝ) ^ k))
    (hr64 : r ≤ 1 / 64) (hw : HalfWidthAt g r a) :
    WeilPrimeSumV1
        (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3))) =
      WeilPrimeTermV1
        (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)))
        (3 ^ k - 1) := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single (3 ^ k - 1)
  intro n hn
  have hne : n + 1 ≠ 3 ^ k := by omega
  have hp := gap_mixed_nat_zero_three g r a k hk hr64 hw (n + 1) (by omega)
  have hi := gap_mixed_inv_nat_zero_three
    g r a k hk hr0 hr hw (n + 1) (by omega) hne
  simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

theorem exp_k_log_three (k : ℕ) :
    Real.exp (k * Real.log 3) = (3 : ℝ) ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem gap_mixed_reciprocal_center_three
    (g : WeilCompactSmoothGV1) (k : ℕ) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 3))
        (((3 : ℝ) ^ k)⁻¹) =
      ((triadicHalf k)⁻¹ : ℝ) * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g 0 (k * Real.log 3)
  have hx : Real.exp (0 - k * Real.log 3) = ((3 : ℝ) ^ k)⁻¹ := by
    rw [zero_sub, Real.exp_neg, exp_k_log_three]
  have hc : Real.exp ((0 - k * Real.log 3) / 2) = triadicHalf k := by
    unfold triadicHalf
    congr 1
    ring
  rw [hx, hc] at h
  have hne : (triadicHalf k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (triadicHalf_pos k))
  rw [Complex.ofReal_inv]
  field_simp
  rw [← h]
  ring

theorem vonMangoldt_three_pow (k : ℕ) (hk : 1 ≤ k) :
    ArithmeticFunction.vonMangoldt (3 ^ k) = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
  exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)

theorem gap_prime_sum_exact_three
    (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 * (3 : ℝ) ^ k))
    (hr64 : r ≤ 1 / 64) (hw : HalfWidthAt g r a) :
    WeilPrimeSumV1
        (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3))) =
      ((Real.log 3 * triadicHalf k * energy g.1 : ℝ) : ℂ) := by
  rw [gap_prime_sum_single_three g r a k hk hr0 hr hr64 hw]
  have hidx : 3 ^ k - 1 + 1 = 3 ^ k :=
    Nat.sub_add_cancel (Nat.one_le_pow k 3 (by norm_num))
  have hpP :
      mixed (translatePacket g 0) (translatePacket g (k * Real.log 3))
        (((3 ^ k : ℕ) : ℝ)) = 0 :=
    gap_mixed_nat_zero_three g r a k hk hr64 hw (3 ^ k) (by positivity)
  have hcast : ((3 ^ k : ℕ) : ℝ) = (3 : ℝ) ^ k := by
    push_cast
    ring
  unfold WeilPrimeTermV1
  simp only [hidx]
  rw [hpP, hcast, gap_mixed_reciprocal_center_three g k,
    vonMangoldt_three_pow k hk]
  have hd :
      ((3 : ℝ) ^ k)⁻¹ * (triadicHalf k)⁻¹ = triadicHalf k := by
    unfold triadicHalf
    rw [← exp_k_log_three, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  push_cast
  have hd' :
      ((3 : ℂ) ^ k)⁻¹ * ((triadicHalf k : ℂ))⁻¹ =
        (triadicHalf k : ℂ) := by
    have hdc := congrArg (fun x : ℝ => (x : ℂ)) hd
    push_cast at hdc
    exact hdc
  rw [zero_add, ← mul_assoc
    (1 / (3 : ℂ) ^ k) ((triadicHalf k : ℂ))⁻¹ (energy g.1 : ℂ),
    one_div, hd']
  ring

theorem gap_B_norm_bound_three
    (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 * (3 : ℝ) ^ k))
    (hr64 : r ≤ 1 / 64) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    ‖B (translatePacket g 0) (translatePacket g (k * Real.log 3))‖ ≤
      (Real.log 3 * triadicHalf k + 1 / 100) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hret := halfWidth_implies_retained g r a hr64 hw
  have hc : 0 ≤ Real.log 3 * triadicHalf k :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (triadicHalf_pos k).le
  have hp :
      ‖WeilPrimeSumV1
          (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)))‖ =
        Real.log 3 * triadicHalf k * energy g.1 := by
    rw [gap_prime_sum_exact_three g r a k hk hr0 hr hr64 hw,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc hE)]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgap : Real.log 2 ≤ k * Real.log 3 := by
    nlinarith [log_two_lt_log_three,
      Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  have ha := translated_arch_norm_bound
    g a 0 (k * Real.log 3) hret hm (by simpa using hgap)
  have hz :
      mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)) 1 = 0 := by
    simpa using gap_mixed_nat_zero_three g r a k hk hr64 hw 1 (by norm_num)
  unfold B WeilExplicitRightSideV1
  rw [hz, mul_zero, add_zero]
  calc
    _ ≤
        ‖WeilPrimeSumV1
            (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)))‖ +
          ‖WeilArchimedeanIntegralV1
            (mixed (translatePacket g 0) (translatePacket g (k * Real.log 3)))‖ :=
      norm_add_le _ _
    _ ≤ Real.log 3 * triadicHalf k * energy g.1 +
          (1 / 100 : ℝ) * energy g.1 := by
      rw [hp]
      exact add_le_add le_rfl ha
    _ = _ := by ring

#print axioms AEGIS.RHPrimeThreeWindowV1.nat_eq_pow_three_of_log_window
#print axioms AEGIS.RHPrimeThreeWindowV1.gap_prime_sum_exact_three
#print axioms AEGIS.RHPrimeThreeWindowV1.gap_B_norm_bound_three

end AEGIS.RHPrimeThreeWindowV1
