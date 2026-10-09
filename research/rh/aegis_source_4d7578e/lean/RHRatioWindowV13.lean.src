import RHDyadicWindowV13
import Mathlib.Tactic

/-!
AEGIS Ω — cross terms at an arbitrary gap with a prime-power-free window, V13.

For a packet of log-half-width `r` and any gap `d ≥ log 2`, the cross term
`B(T_{d₁} g, T_{d₂} g)` with `d₂ − d₁ = d` sees only the integers `m` with
`|log m − d| ≤ 2r`.  If none of those is a prime power, the prime sum vanishes
exactly and only the Archimedean part remains:

  ‖B(T_{d₁} g, T_{d₂} g)‖ ≤ (1/100) · E(g).

This is the lemma behind non-integer lattice ratios (e.g. `q = 33/16`): the
windows around `q^k` can avoid prime powers entirely for many `k`, which no
dyadic lattice can do.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHRatioWindowV13
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHDyadicWindowV13
open AEGIS.RHFourBlockPrimeEightV3

/-- No prime power in the log-window of radius `2r` around `d`. -/
def PrimePowerFreeWindow (d r : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → |Real.log (m : ℝ) - d| ≤ 2 * r → ArithmeticFunction.vonMangoldt m = 0

theorem mixed_nat_zero_of_gap (g : WeilCompactSmoothGV1) (r a d : ℝ) (hr0 : 0 < r)
    (hd : 2 * r < d) (hw : HalfWidthAt g r a) (m : ℕ) (hm : 0 < m) :
    mixed (translatePacket g 0) (translatePacket g d) (m : ℝ) = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_nonneg hm1
  have hfar : 2 * r < |Real.log (m : ℝ) + d - 0| := by
    rw [abs_of_pos (by linarith)]; linarith
  have hz := mixed_translate_zero_of_halfWidth g r a 0 d (Real.log (m : ℝ)) hw hfar
  simpa only [Real.exp_log hmpos] using hz

theorem prime_sum_zero_of_window (g : WeilCompactSmoothGV1) (r a d : ℝ) (hr0 : 0 < r)
    (hd : 2 * r < d) (hw : HalfWidthAt g r a) (hΛ : PrimePowerFreeWindow d r) :
    WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g d)) = 0 := by
  unfold WeilPrimeSumV1
  have hterm : ∀ n : ℕ, WeilPrimeTermV1 (mixed (translatePacket g 0) (translatePacket g d)) n = 0 := by
    intro n
    have hp := mixed_nat_zero_of_gap g r a d hr0 hd hw (n + 1) (by omega)
    unfold WeilPrimeTermV1
    simp only [hp, zero_add]
    by_cases hwin : |Real.log ((n + 1 : ℕ) : ℝ) - d| ≤ 2 * r
    · rw [hΛ (n + 1) (by omega) hwin]
      simp
    · have hfar0 : 2 * r < |Real.log ((n + 1 : ℕ) : ℝ) - d| := lt_of_not_ge hwin
      have hfar : 2 * r < |-Real.log ((n + 1 : ℕ) : ℝ) + d - 0| := by
        rw [show -Real.log ((n + 1 : ℕ) : ℝ) + d - 0 = -(Real.log ((n + 1 : ℕ) : ℝ) - d) by ring,
          abs_neg]
        exact hfar0
      have hz := mixed_translate_zero_of_halfWidth g r a 0 d (-Real.log ((n + 1 : ℕ) : ℝ)) hw hfar
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have he : Real.exp (-Real.log ((n + 1 : ℕ) : ℝ)) = (((n + 1 : ℕ) : ℝ))⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hpos]
      rw [he] at hz
      rw [hz]
      simp
  simp only [hterm, tsum_zero]

/-- With a prime-power-free window only the Archimedean part survives. -/
theorem B_norm_le_arch_of_window (g : WeilCompactSmoothGV1) (r a d : ℝ) (hr0 : 0 < r)
    (hr64 : r ≤ 1 / 64) (hd : Real.log 2 ≤ d) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) (hΛ : PrimePowerFreeWindow d r) :
    ‖B (translatePacket g 0) (translatePacket g d)‖ ≤ (1 / 100 : ℝ) * energy g.1 := by
  have hret := halfWidth_implies_retained g r a hr64 hw
  have hd' : 2 * r < d := by linarith [log_two_lower]
  have hz1 : mixed (translatePacket g 0) (translatePacket g d) 1 = 0 := by
    simpa using mixed_nat_zero_of_gap g r a d hr0 hd' hw 1 (by norm_num)
  have ha := translated_arch_norm_bound g a 0 d hret hm (by linarith)
  unfold B WeilExplicitRightSideV1
  rw [prime_sum_zero_of_window g r a d hr0 hd' hw hΛ, hz1, mul_zero, add_zero, zero_add]
  exact ha

theorem B_norm_le_arch_of_window_pair (g : WeilCompactSmoothGV1) (r a d1 d2 : ℝ) (hr0 : 0 < r)
    (hr64 : r ≤ 1 / 64) (hd : Real.log 2 ≤ d2 - d1) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) (hΛ : PrimePowerFreeWindow (d2 - d1) r) :
    ‖B (translatePacket g d1) (translatePacket g d2)‖ ≤ (1 / 100 : ℝ) * energy g.1 := by
  rw [B_translate_eq_of_gap_v3 g d1 d2 0 (d2 - d1) (by ring)]
  exact B_norm_le_arch_of_window g r a (d2 - d1) hr0 hr64 hd hw hm hΛ

end AEGIS.RHRatioWindowV13

#print axioms AEGIS.RHRatioWindowV13.prime_sum_zero_of_window
#print axioms AEGIS.RHRatioWindowV13.B_norm_le_arch_of_window_pair
