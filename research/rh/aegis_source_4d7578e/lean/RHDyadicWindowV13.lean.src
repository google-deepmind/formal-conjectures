import RHDyadicDiagonalV13
import RHFourBlockPrimeEightV3
import Mathlib.Tactic

/-!
AEGIS Ω — dyadic-gap cross terms at every half-width, V13.

Arithmetic half of the width pattern.  For a moment-zero packet of log-half-width
`r`, the cross term at gap `k · log 2` sees only the integers `m` with
`|log m − k·log 2| ≤ 2r`; when `2r ≤ 2^{-(k+1)}` the only such integer is
`m = 2^k`, whose von Mangoldt weight is `log 2`.  Hence

  ‖B(T₀ g, T_{k log 2} g)‖ ≤ (log 2 · e^{−k log 2 / 2} + 1/100) · E(g),

a geometric series in `k`, uniformly in the width.  This generalises the
`k = 3` computation of `RHFourBlockPrimeEightV3` to every `k ≥ 1`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHDyadicWindowV13
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
open AEGIS.RHFourBlockPrimeEightV3

/-! ### The support window at half-width `r` -/

theorem logCorrelation_zero_of_halfWidth (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < |u|) :
    logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hm0 : v ∈ tsupport (logLift g.1) := subset_tsupport _ h0
      have hm1 : v + u ∈ tsupport (logLift g.1) := subset_tsupport _ h1
      have hv := hw hm0
      have hvu := hw hm1
      have habs : |u| ≤ 2 * r := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

theorem mixed_translate_zero_of_halfWidth (g : WeilCompactSmoothGV1) (r a d1 d2 u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < |u + d2 - d1|) :
    mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u) = 0 := by
  have h := exp_half_mul_mixed_translate_v28 g d1 d2 u
  rw [logCorrelation_zero_of_halfWidth g r a (u + d2 - d1) hw hu] at h
  have he : (Real.exp (u / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp h).resolve_left he

/-! ### The only integer in the gap-`k` window is `2^k` -/

theorem nat_eq_pow_of_log_window (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 < r)
    (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1))
    {m : ℕ} (hm : 0 < m) (hw : |Real.log (m : ℝ) - k * Real.log 2| ≤ 2 * r) :
    m = 2 ^ k := by
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have hP2 : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  have hlogP : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := by rw [Real.log_pow]
  have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hsmall : 2 * r * (2 * 2 ^ k) ≤ 1 := by
    rw [h2k] at hr
    rwa [le_div_iff₀ (by positivity)] at hr
  have h2r1 : 2 * r < 1 := by nlinarith
  have hup : (m : ℝ) ≤ 2 ^ k * Real.exp (2 * r) := by
    have := Real.exp_le_exp.mpr (show Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ k) + 2 * r by
      rw [hlogP]; linarith)
    rwa [Real.exp_add, Real.exp_log hP, Real.exp_log hmpos] at this
  have hlo : 2 ^ k * Real.exp (-(2 * r)) ≤ (m : ℝ) := by
    have := Real.exp_le_exp.mpr (show Real.log ((2 : ℝ) ^ k) - 2 * r ≤ Real.log (m : ℝ) by
      rw [hlogP]; linarith)
    rwa [sub_eq_add_neg, Real.exp_add, Real.exp_log hP, Real.exp_log hmpos] at this
  have hexp_up : Real.exp (2 * r) ≤ 1 / (1 - 2 * r) :=
    Real.exp_bound_div_one_sub_of_interval (by linarith) h2r1
  have hexp_lo : 1 - 2 * r ≤ Real.exp (-(2 * r)) := by
    linarith [Real.add_one_le_exp (-(2 * r))]
  have hlt : (m : ℝ) < 2 ^ k + 1 := by
    calc (m : ℝ) ≤ 2 ^ k * Real.exp (2 * r) := hup
      _ ≤ 2 ^ k * (1 / (1 - 2 * r)) := mul_le_mul_of_nonneg_left hexp_up hP.le
      _ < 2 ^ k + 1 := by
        rw [mul_one_div, div_lt_iff₀ (by linarith)]
        nlinarith
  have hgt : (2 : ℝ) ^ k < m + 1 := by
    calc (2 : ℝ) ^ k < 2 ^ k * (1 - 2 * r) + 1 := by nlinarith
      _ ≤ 2 ^ k * Real.exp (-(2 * r)) + 1 := by
          linarith [mul_le_mul_of_nonneg_left hexp_lo hP.le]
      _ ≤ m + 1 := by linarith
  have h1 : m < 2 ^ k + 1 := by exact_mod_cast hlt
  have h2 : 2 ^ k < m + 1 := by exact_mod_cast hgt
  omega

/-! ### Vanishing of all but the dyadic sample -/

theorem gap_mixed_nat_zero (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr64 : r ≤ 1 / 64) (hw : HalfWidthAt g r a) (m : ℕ) (hm : 0 < m) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)) (m : ℝ) = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm := Real.log_nonneg hm1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < Real.log (m : ℝ) + k * Real.log 2 - 0 := by
    nlinarith [log_two_lower]
  have hfar : 2 * r < |Real.log (m : ℝ) + k * Real.log 2 - 0| := by
    rw [abs_of_pos hpos]
    nlinarith [log_two_lower]
  have hz := mixed_translate_zero_of_halfWidth g r a 0 (k * Real.log 2) (Real.log (m : ℝ)) hw hfar
  simpa only [Real.exp_log hmpos] using hz

theorem gap_mixed_inv_nat_zero (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1)) (hw : HalfWidthAt g r a)
    (m : ℕ) (hm : 0 < m) (hne : m ≠ 2 ^ k) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)) ((m : ℝ)⁻¹) = 0 := by
  have hfar0 : 2 * r < |Real.log (m : ℝ) - k * Real.log 2| := by
    by_contra h
    exact hne (nat_eq_pow_of_log_window k hk r hr0 hr hm (le_of_not_gt h))
  have ha : -Real.log (m : ℝ) + k * Real.log 2 - 0 = -(Real.log (m : ℝ) - k * Real.log 2) := by
    ring
  have hfar : 2 * r < |-Real.log (m : ℝ) + k * Real.log 2 - 0| := by
    rw [ha, abs_neg]; exact hfar0
  have hz := mixed_translate_zero_of_halfWidth g r a 0 (k * Real.log 2) (-Real.log (m : ℝ)) hw hfar
  have he : Real.exp (-Real.log (m : ℝ)) = (m : ℝ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hm)]
  simpa only [he] using hz

theorem gap_prime_sum_single (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1)) (hr64 : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) :
    WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (k * Real.log 2))) =
      WeilPrimeTermV1 (mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)))
        (2 ^ k - 1) := by
  unfold WeilPrimeSumV1
  have hP1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  apply tsum_eq_single (2 ^ k - 1)
  intro n hn
  have hne : n + 1 ≠ 2 ^ k := by omega
  have hp := gap_mixed_nat_zero g r a k hk hr64 hw (n + 1) (by omega)
  have hi := gap_mixed_inv_nat_zero g r a k hk hr0 hr hw (n + 1) (by omega) hne
  simp only [WeilPrimeTermV1, hp, hi, mul_zero, add_zero]

/-! ### The dyadic sample -/

/-- `2^{-k/2}` in exponential form. -/
def dyadicHalf (k : ℕ) : ℝ := Real.exp (-(k * Real.log 2) / 2)

theorem dyadicHalf_pos (k : ℕ) : 0 < dyadicHalf k := Real.exp_pos _

theorem exp_k_log_two (k : ℕ) : Real.exp (k * Real.log 2) = (2 : ℝ) ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem gap_mixed_reciprocal_center (g : WeilCompactSmoothGV1) (k : ℕ) :
    mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)) (((2 : ℝ) ^ k)⁻¹) =
      ((dyadicHalf k)⁻¹ : ℝ) * (energy g.1 : ℂ) := by
  have h := mixed_translate_center_v28 g 0 (k * Real.log 2)
  have hx : Real.exp (0 - k * Real.log 2) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [zero_sub, Real.exp_neg, exp_k_log_two]
  have hc : Real.exp ((0 - k * Real.log 2) / 2) = dyadicHalf k := by
    unfold dyadicHalf; congr 1; ring
  rw [hx, hc] at h
  have hne : (dyadicHalf k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (dyadicHalf_pos k))
  rw [Complex.ofReal_inv]
  field_simp
  rw [← h]
  ring

theorem vonMangoldt_two_pow (k : ℕ) (hk : 1 ≤ k) :
    ArithmeticFunction.vonMangoldt (2 ^ k) = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
  exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)

theorem gap_prime_sum_exact (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1)) (hr64 : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) :
    WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (k * Real.log 2))) =
      ((Real.log 2 * dyadicHalf k * energy g.1 : ℝ) : ℂ) := by
  rw [gap_prime_sum_single g r a k hk hr0 hr hr64 hw]
  have hP1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hidx : 2 ^ k - 1 + 1 = 2 ^ k := by omega
  have hpP : mixed (translatePacket g 0) (translatePacket g (k * Real.log 2))
      (((2 ^ k : ℕ) : ℝ)) = 0 :=
    gap_mixed_nat_zero g r a k hk hr64 hw (2 ^ k) (by omega)
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  unfold WeilPrimeTermV1
  simp only [hidx]
  rw [hpP, hcast, gap_mixed_reciprocal_center g k, vonMangoldt_two_pow k hk]
  -- Λ(2^k) · (0 + (1/2^k) · (dyadicHalf k)⁻¹ · E) = log 2 · dyadicHalf k · E
  have hd : ((2 : ℝ) ^ k)⁻¹ * (dyadicHalf k)⁻¹ = dyadicHalf k := by
    unfold dyadicHalf
    rw [← exp_k_log_two, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  push_cast
  have hd' : ((2 : ℂ) ^ k)⁻¹ * ((dyadicHalf k : ℂ))⁻¹ = (dyadicHalf k : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hd
    push_cast at this
    exact this
  rw [zero_add, ← mul_assoc (1 / (2 : ℂ) ^ k) ((dyadicHalf k : ℂ))⁻¹ (energy g.1 : ℂ), one_div, hd']
  ring

/-! ### The cross-term ceiling at every dyadic gap -/

theorem gap_B_norm_bound (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1)) (hr64 : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    ‖B (translatePacket g 0) (translatePacket g (k * Real.log 2))‖ ≤
      (Real.log 2 * dyadicHalf k + 1 / 100) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hret := halfWidth_implies_retained g r a hr64 hw
  have hc : 0 ≤ Real.log 2 * dyadicHalf k :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (dyadicHalf_pos k).le
  have hp : ‖WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)))‖ =
      Real.log 2 * dyadicHalf k * energy g.1 := by
    rw [gap_prime_sum_exact g r a k hk hr0 hr hr64 hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc hE)]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha := translated_arch_norm_bound g a 0 (k * Real.log 2) hret hm
    (by nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hz : mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)) 1 = 0 := by
    simpa using gap_mixed_nat_zero g r a k hk hr64 hw 1 (by norm_num)
  unfold B WeilExplicitRightSideV1
  rw [hz, mul_zero, add_zero]
  calc
    _ ≤ ‖WeilPrimeSumV1 (mixed (translatePacket g 0) (translatePacket g (k * Real.log 2)))‖ +
        ‖WeilArchimedeanIntegralV1 (mixed (translatePacket g 0)
          (translatePacket g (k * Real.log 2)))‖ := norm_add_le _ _
    _ ≤ Real.log 2 * dyadicHalf k * energy g.1 + (1 / 100 : ℝ) * energy g.1 := by
      rw [hp]; exact add_le_add le_rfl ha
    _ = _ := by ring

/-- Any two translates with gap `k · log 2` have the same ceiling. -/
theorem gap_B_norm_bound_pair (g : WeilCompactSmoothGV1) (r a : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : 0 < r) (hr : 2 * r ≤ 1 / (2 : ℝ) ^ (k + 1)) (hr64 : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) (d1 d2 : ℝ)
    (hgap : d2 - d1 = k * Real.log 2) :
    ‖B (translatePacket g d1) (translatePacket g d2)‖ ≤
      (Real.log 2 * dyadicHalf k + 1 / 100) * energy g.1 := by
  rw [B_translate_eq_of_gap_v3 g d1 d2 0 (k * Real.log 2) (by linarith)]
  exact gap_B_norm_bound g r a k hk hr0 hr hr64 hw hm

end AEGIS.RHDyadicWindowV13

#print axioms AEGIS.RHDyadicWindowV13.nat_eq_pow_of_log_window
#print axioms AEGIS.RHDyadicWindowV13.gap_prime_sum_exact
#print axioms AEGIS.RHDyadicWindowV13.gap_B_norm_bound
#print axioms AEGIS.RHDyadicWindowV13.gap_B_norm_bound_pair
