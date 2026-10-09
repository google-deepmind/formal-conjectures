import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
AEGIS Ω — elementary analytic constants for the three-block Weil certificate V2.1

LOCAL CANDIDATE / FORMAL_MATH_EVIDENCE_ONLY / NOT_YET_KERNEL_REPLAYED.

Purpose:
bind the elementary numerical inequalities used by the written width-1/32
three-block certificate directly to the pinned Mathlib surface.

This file proves no Weil sign by itself.  In particular it does NOT prove:
* the diagonal kernel inequality D/H >= ...;
* the separated moment-zero Archimedean estimate;
* the prime-window identification;
* global Weil nonpositivity or RH.
-/

open scoped BigOperators
noncomputable section

namespace AEGIS.WeilThreeBlockAnalyticConstantsV21

theorem log_two_lower :
    (693 : ℝ) / 1000 < Real.log 2 := by
  exact (by norm_num : (693 : ℝ) / 1000 < 0.6931471803).trans Real.log_two_gt_d9

theorem log_two_upper :
    Real.log 2 < (7 : ℝ) / 10 := by
  exact Real.log_two_lt_d9.trans (by norm_num)

theorem sqrt_two_lower :
    (7 : ℝ) / 5 < Real.sqrt 2 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith

theorem exp_one_over_64_upper :
    Real.exp ((1 : ℝ) / 64) < (64 : ℝ) / 63 := by
  calc
    Real.exp ((1 : ℝ) / 64)
        < 1 / (1 - (1 : ℝ) / 64) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ = (64 : ℝ) / 63 := by norm_num

theorem exp_five_over_64_upper :
    Real.exp ((5 : ℝ) / 64) < (64 : ℝ) / 59 := by
  calc
    Real.exp ((5 : ℝ) / 64)
        < 1 / (1 - (5 : ℝ) / 64) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ = (64 : ℝ) / 59 := by norm_num

theorem exp_one_over_16_upper :
    Real.exp ((1 : ℝ) / 16) < (16 : ℝ) / 15 := by
  calc
    Real.exp ((1 : ℝ) / 16)
        < 1 / (1 - (1 : ℝ) / 16) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ = (16 : ℝ) / 15 := by norm_num

/-- A small finite Taylor lower bound, used only to turn a π upper bound
into the certificate's `log (4π) < 633/250` inequality. -/
theorem exp_633_over_250_gt_88_over_7 :
    (88 : ℝ) / 7 < Real.exp ((633 : ℝ) / 250) := by
  have h :=
    Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ (633 : ℝ) / 250) 10
  have hs :
      (88 : ℝ) / 7 <
        ∑ i ∈ Finset.range 10,
          (((633 : ℝ) / 250) ^ i) / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  exact hs.trans_le h

theorem log_four_pi_upper :
    Real.log (4 * Real.pi) < (633 : ℝ) / 250 := by
  rw [Real.log_lt_iff_lt_exp (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (4 : ℝ) * Real.pi < 4 * 3.1416 :=
      mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
    _ < (88 : ℝ) / 7 := by norm_num
    _ < Real.exp ((633 : ℝ) / 250) := exp_633_over_250_gt_88_over_7

/-- Exact rational value used only to make the γ bound a small trusted-kernel
specialization of Mathlib's monotone Euler-Mascheroni upper sequence. -/
theorem harmonic_256_exact :
    harmonic 256 =
      (102120333780755602922415011407986918913493325085710168750386125102325162741298648605491283438121466698312402217 : ℚ) /
      (16674490806895842671659008751776385350270324508909651849955453691538889375930032935391666564679008085339616000 : ℚ) := by
  set_option maxRecDepth 100000 in
    norm_num [harmonic]

theorem euler_mascheroni_upper :
    Real.eulerMascheroniConstant < (29 : ℝ) / 50 := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  have hseq :
      Real.eulerMascheroniSeq' 256 =
        ((harmonic 256 : ℚ) : ℝ) - Real.log (256 : ℝ) := by
    set_option maxRecDepth 100000 in
      simp [Real.eulerMascheroniSeq']
  rw [hseq] at hγ
  have hlog256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    calc
      Real.log (256 : ℝ) = Real.log ((2 : ℝ) ^ 8) := by norm_num
      _ = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [hlog256] at hγ
  have hH :
      (((harmonic 256 : ℚ) : ℝ) - 8 * (0.6931471803 : ℝ))
        < (29 : ℝ) / 50 := by
    rw [harmonic_256_exact]
    norm_num
  nlinarith [Real.log_two_gt_d9]

theorem prime_adjacent_scalar_upper :
    Real.log 2 / Real.sqrt 2 < (1 : ℝ) / 2 := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hspos]
  nlinarith [log_two_upper, sqrt_two_lower]

theorem prime_outer_scalar_upper :
    Real.log 2 / 2 < (7 : ℝ) / 20 := by
  nlinarith [log_two_upper]

/-- The complete elementary constant margin needed after the analytic diagonal
kernel has been reduced to
`log(coth(1/64)) - log(4π) - γ - (1/64) exp(1/64)`.
No kernel identity is asserted here. -/
theorem diagonal_constant_floor :
    (32449 : ℝ) / 31500 <
      6 * Real.log 2
        - Real.log (4 * Real.pi)
        - Real.eulerMascheroniConstant
        - ((1 : ℝ) / 64) * Real.exp ((1 : ℝ) / 64) := by
  have hsmall :
      ((1 : ℝ) / 64) * Real.exp ((1 : ℝ) / 64) < (1 : ℝ) / 63 := by
    nlinarith [exp_one_over_64_upper]
  nlinarith [log_two_lower, log_four_pi_upper, euler_mascheroni_upper, hsmall]

theorem certificate_diagonal_threshold :
    (103 : ℝ) / 100 < (32449 : ℝ) / 31500 := by
  norm_num

end AEGIS.WeilThreeBlockAnalyticConstantsV21
