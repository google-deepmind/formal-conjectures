import RHHalfCapGainV13
import WeilThreeBlockAnalyticConstantsV21
import Mathlib.Tactic

/-!
AEGIS Ω — Weil positivity on the half-width-11/64 class via the half-cap, V13.

`halfGain (11/64) ≤ −1/20` (true value ≈ −0.1345), hence every moment-zero packet
whose logarithmic support has half-width at most `11/64` (support length `≤ 11/32`)
has `Re RHS ≤ −E/20` and a nonnegative canonical zero quadratic.  This extends the
moment-gain class (`1/8`) and the closed-form ceiling of that route (`≈ 0.161`).

Numerics: with `q = e^{−11/64}`, `cothTail(11/32) − 3·cothTail(11/64) =
log((1+q²)(1−q)²/(1+q)⁴) ≤ −8·log 2`; the λ-term equals
`(2c − 3)/(c(1+q))` with `c = cosh(11/128)` and is `≤ −1/2`; Taylor enclosures come
from `Real.exp_bound`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHalfCapClassV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHHalfCapGainV13

theorem exp_neg_11_64_bounds :
    (8420038 / 10000000 : ℝ) ≤ Real.exp (-(11 / 64)) ∧
      Real.exp (-(11 / 64)) ≤ (8420948 / 10000000 : ℝ) := by
  have h := Real.exp_bound (x := -(11 / 64 : ℝ))
    (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) (n := 4) (by norm_num)
  have h' := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  obtain ⟨h1, h2⟩ := h'
  constructor <;> linarith

theorem exp_11_128_upper : Real.exp (11 / 128) ≤ (10898 / 10000 : ℝ) := by
  have h := Real.exp_bound (x := (11 / 128 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 3) (by norm_num)
  have h' := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  linarith [h'.2]

theorem exp_neg_11_128_upper : Real.exp (-(11 / 128)) ≤ (9179 / 10000 : ℝ) := by
  have h := Real.exp_bound (x := -(11 / 128 : ℝ))
    (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) (n := 3) (by norm_num)
  have h' := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  linarith [h'.2]

/-- `cothTail(11/32) − 3·cothTail(11/64) ≤ −8·log 2`. -/
theorem cothTail_combo_11_64 :
    cothTail (2 * (11 / 64)) - 3 * cothTail (11 / 64) ≤ -(8 * Real.log 2) := by
  obtain ⟨hlo, hhi⟩ := exp_neg_11_64_bounds
  set q := Real.exp (-(11 / 64 : ℝ)) with hqdef
  have hq2 : Real.exp (-(2 * (11 / 64 : ℝ))) = q ^ 2 := by
    rw [hqdef, sq, ← Real.exp_add]; ring_nf
  have hq1 : q < 1 := by linarith
  unfold cothTail
  rw [hq2]
  have h1q : 0 < 1 - q := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by nlinarith
  have hX : 0 < (1 + q ^ 2) / (1 - q ^ 2) := div_pos (by positivity) h1q2
  have hY : 0 < (1 + q) / (1 - q) := div_pos (by linarith) h1q
  -- 256 (1+q²)(1−q)² ≤ (1+q)⁴
  have hA : (1 + q ^ 2) * (1 - q) ^ 2 ≤
      (1 + (8420948 / 10000000 : ℝ) ^ 2) * (1 - (8420038 / 10000000 : ℝ)) ^ 2 := by
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · nlinarith
    · apply pow_le_pow_left₀ h1q.le (by linarith)
  have hB : (1 + (8420038 / 10000000 : ℝ)) ^ 4 ≤ (1 + q) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hpoly : 256 * ((1 + q ^ 2) * (1 - q) ^ 2) ≤ (1 + q) ^ 4 := by
    have hnum : 256 * ((1 + (8420948 / 10000000 : ℝ) ^ 2) * (1 - (8420038 / 10000000 : ℝ)) ^ 2) ≤
        (1 + (8420038 / 10000000 : ℝ)) ^ 4 := by norm_num
    nlinarith
  have hXY : (1 + q ^ 2) / (1 - q ^ 2) * 2 ^ 8 ≤ ((1 + q) / (1 - q)) ^ 3 := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ h1q2 (by positivity)]
    have hsq : (1 - q ^ 2) = (1 - q) * (1 + q) := by ring
    rw [hsq]
    have hpos : 0 < (1 - q) := h1q
    nlinarith [mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ (1 - q) * (1 + q) ^ 0),
      pow_pos hpos 2, pow_pos hpos 3]
  have hlog := Real.log_le_log (by positivity) hXY
  rw [Real.log_mul hX.ne' (by positivity), Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- The λ-term at `11/64` is at most `−1/2`. -/
theorem lam_term_11_64 :
    2 * lamR (11 / 64) * (Real.sinh (11 / 64) - 3 * Real.sinh ((11 / 64) / 2)) ≤ -(1 / 2) := by
  have hs : 0 < Real.sinh ((11 / 64 : ℝ) / 2) := Real.sinh_pos_iff.mpr (by norm_num)
  have hc1 : 1 ≤ Real.cosh ((11 / 64 : ℝ) / 2) := Real.one_le_cosh _
  have hsr : Real.sinh (11 / 64 : ℝ) =
      2 * Real.sinh ((11 / 64 : ℝ) / 2) * Real.cosh ((11 / 64 : ℝ) / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have he := Real.exp_pos (-(11 / 64 : ℝ))
  obtain ⟨_, hqhi⟩ := exp_neg_11_64_bounds
  have hc : Real.cosh ((11 / 64 : ℝ) / 2) ≤ (10039 / 10000 : ℝ) := by
    rw [show (11 / 64 : ℝ) / 2 = 11 / 128 by norm_num, Real.cosh_eq]
    linarith [exp_11_128_upper, exp_neg_11_128_upper]
  unfold lamR
  rw [hsr]
  set s := Real.sinh ((11 / 64 : ℝ) / 2)
  set c := Real.cosh ((11 / 64 : ℝ) / 2)
  set e := Real.exp (-(11 / 64 : ℝ))
  have hden : 0 < 2 * s * c * (1 + e) := by positivity
  rw [show 2 * (1 / (2 * s * c * (1 + e))) * (2 * s * c - 3 * s) =
      (2 * (2 * s * c - 3 * s)) / (2 * s * c * (1 + e)) by ring, div_le_iff₀ hden]
  nlinarith [mul_pos hs (by linarith : (0:ℝ) < c)]

/-- `halfGain (11/64) ≤ −1/20` (true value ≈ −0.1345). -/
theorem halfGain_11_64 : halfGain (11 / 64) ≤ -(1 / 20) := by
  have hcombo := cothTail_combo_11_64
  have hlam := lam_term_11_64
  have hexp := exp_11_128_upper
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 := log_two_lower
  unfold halfGain
  rw [show (11 / 64 : ℝ) / 2 = 11 / 128 by norm_num] at *
  have hpos := Real.exp_pos (11 / 128 : ℝ)
  nlinarith

theorem half_cap_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (11 / 64) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 20) * energy g.1 := by
  have hlog : 2 * (11 / 64 : ℝ) < Real.log 2 := by linarith [log_two_lower]
  have hd := half_cap_diagonal g (11 / 64) a (by norm_num) hlog hw hm
  have hg := mul_le_mul_of_nonneg_right halfGain_11_64 (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`11/64` class.** -/
theorem universal_on_half_cap_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (11 / 64) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := half_cap_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHalfCapClassV13

#print axioms AEGIS.RHHalfCapClassV13.halfGain_11_64
#print axioms AEGIS.RHHalfCapClassV13.half_cap_coercive
#print axioms AEGIS.RHHalfCapClassV13.universal_on_half_cap_class
