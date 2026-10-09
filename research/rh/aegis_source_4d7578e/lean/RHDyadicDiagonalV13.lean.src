import RHNarrowDiagonalUpgradeV2
import Mathlib.Tactic

/-!
AEGIS Ω — the diagonal at every width, V13.

The repository proves the diagonal floor `103/100 · E` at log-half-width `1/64`
and `32/25 · E` at half-width `1/128`, each with a hand-tuned shell estimate.
Underneath, every ingredient is parametric: `logCross_zero_outside` takes
arbitrary supports and `integral_one_div_sinh_Ioi` is stated for every lower
limit.  This module states the diagonal for every half-width `0 < r ≤ 1/64`:

  E · ( log((1+e^{-2r})/(1−e^{-2r})) − κ − r·e^{1/64} ) ≤ −Re B(g, g),

with `κ = log(4π) + γ`.  The coth tail `log((1+e^{-2r})/(1−e^{-2r}))` grows
like `log(1/r)`: the diagonal is unbounded as the packet narrows.  This is the
analytic half of the pattern "narrower packets certify more dyadic
translates".  The arithmetic half (single dyadic sample per window) is a
separate module.  Neither is RH.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilArchimedeanCothTailV1
open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHNarrowDiagonalUpgradeV2

/-- Log-support inside `[a − r, a + r]`. -/
def HalfWidthAt (g : WeilCompactSmoothGV1) (r a : ℝ) : Prop :=
  LogSupportIn g (a - r) (a + r)

/-- The coth tail `∫_{w}^{∞} du / sinh u`. -/
def cothTail (w : ℝ) : ℝ :=
  Real.log ((1 + Real.exp (-w)) / (1 - Real.exp (-w)))

theorem halfWidth_implies_retained (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hr : r ≤ 1 / 64) (hw : HalfWidthAt g r a) : WidthOneThirtyTwoAt g a := by
  intro t ht
  have h := hw ht
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem halfWidth_1_128_iff (g : WeilCompactSmoothGV1) (a : ℝ) :
    HalfWidthAt g (1 / 128) a ↔ WidthOneSixtyFourAt g a := Iff.rfl

/-- Beyond twice the half-width the autocorrelation vanishes. -/
theorem autocorrelation_zero_of_halfWidth (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : 2 * r < u) :
    WeilAutocorrelationV1 g (Real.exp u) = 0 := by
  have hc := logCross_zero_outside g g (a - r) (a + r) (a - r) (a + r) u hw hw
    (Or.inr (by linarith))
  rw [logCross_eq_mixed_v28] at hc
  have hm := (mul_eq_zero.mp hc).resolve_left (by simp)
  change WeilAutocorrelationV1 g (Real.exp u) = 0 at hm
  exact hm

theorem tail_integrand_eq (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hw : HalfWidthAt g r a) {u : ℝ} (hu : 2 * r < u) :
    widthArchLogIntegrandV26 g u = -energy g.1 / Real.sinh u := by
  unfold widthArchLogIntegrandV26
  rw [autocorrelation_zero_of_halfWidth g r a u hw hu]
  simp

theorem split_at (g : WeilCompactSmoothGV1) (w : ℝ) (hw : 0 ≤ w) :
    (∫ u in Ioi (0 : ℝ), widthArchLogIntegrandV26 g u) =
      (∫ u in Ioc (0 : ℝ) w, widthArchLogIntegrandV26 g u) +
      ∫ u in Ioi w, widthArchLogIntegrandV26 g u := by
  have hfull := width_arch_log_integrableOn_v27 g
  have hinner : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) w) :=
    hfull.mono_set (fun u hu => hu.1)
  have htail : IntegrableOn (widthArchLogIntegrandV26 g) (Ioi w) :=
    hfull.mono_set (by intro u hu; change w < u at hu; change (0 : ℝ) < u; linarith)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hw,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hinner htail]

theorem inner_le (g : WeilCompactSmoothGV1) (w : ℝ) (hw0 : 0 ≤ w) (hw32 : w ≤ 1 / 32) :
    (∫ u in Ioc (0 : ℝ) w, widthArchLogIntegrandV26 g u) ≤
      w * (energy g.1 * (Real.exp (1 / 64 : ℝ) / 2)) := by
  have hfull := width_arch_log_integrableOn_v27 g
  have hinner : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) w) :=
    hfull.mono_set (fun u hu => hu.1)
  calc
    _ ≤ ∫ _u in Ioc (0 : ℝ) w, energy g.1 * (Real.exp (1 / 64 : ℝ) / 2) := by
      apply setIntegral_mono_on hinner continuous_const.integrableOn_Ioc measurableSet_Ioc
      intro u hu
      exact width_arch_log_inner_pointwise_v26 g hu.1 (le_trans hu.2 hw32)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw0]
      ring

theorem tail_eq (g : WeilCompactSmoothGV1) (r a : ℝ) (hr : 0 < r)
    (hw : HalfWidthAt g r a) :
    (∫ u in Ioi (2 * r), widthArchLogIntegrandV26 g u) =
      -energy g.1 * cothTail (2 * r) := by
  calc
    (∫ u in Ioi (2 * r), widthArchLogIntegrandV26 g u)
        = ∫ u in Ioi (2 * r), (-energy g.1) * (1 / Real.sinh u) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          rw [tail_integrand_eq g r a hw hu]
          ring
    _ = (-energy g.1) * ∫ u in Ioi (2 * r), 1 / Real.sinh u := by
          rw [integral_const_mul]
    _ = -energy g.1 * cothTail (2 * r) := by
          rw [integral_one_div_sinh_Ioi (by linarith : (0 : ℝ) < 2 * r)]
          rfl

/-- Archimedean budget at every half-width `0 < r ≤ 1/64`. -/
theorem arch_budget (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r) (hr : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (r * Real.exp (1 / 64 : ℝ) - cothTail (2 * r)) := by
  rw [archimedean_real_eq_log_integral_v27, split_at g (2 * r) (by linarith)]
  have hi := inner_le g (2 * r) (by linarith) (by linarith)
  have ht := tail_eq g r a hr0 hw
  rw [ht]
  nlinarith [energy_nonnegative g.1, Real.exp_pos (1 / 64 : ℝ)]

/-- **The diagonal at every half-width.**  The floor grows like `log(1/r)`. -/
theorem diagonal_lower (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r) (hr : r ≤ 1 / 64)
    (hw : HalfWidthAt g r a) :
    energy g.1 * (cothTail (2 * r) - diagonalKappaV21 - r * Real.exp (1 / 64 : ℝ)) ≤
      -(B g g).re := by
  have hp := width_diagonal_prime_sum_zero_v24 g a (halfWidth_implies_retained g r a hr hw)
  have hb := arch_budget g r a hr0 hr hw
  rw [actual_diagonal_rhs_decomposition g hp]
  nlinarith [energy_nonnegative g.1]

/-- Sanity: at `r = 1/64` this recovers the repository's `103/100` floor route
(`cothTail (1/32) > 6 log 2`, `κ + (1/64)e^{1/64} < 6 log 2 − 103/100`). -/
theorem diagonal_lower_recovers_103_over_100 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 64) a) :
    (103 / 100 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have h := diagonal_lower g (1 / 64) a (by norm_num) le_rfl hw
  have hE := energy_nonnegative g.1
  have htail : 6 * Real.log 2 < cothTail (2 * (1 / 64)) := by
    have := six_log_two_lt_integral_one_div_sinh_Ioi
    rw [integral_one_div_sinh_Ioi (by norm_num : (0 : ℝ) < 1 / 32)] at this
    unfold cothTail
    norm_num at this ⊢
    exact this
  have hc := diagonal_constant_floor
  have hn := certificate_diagonal_threshold
  unfold diagonalKappaV21 at h
  nlinarith [mul_le_mul_of_nonneg_left (le_of_lt htail) hE]


/-! ### Growth of the coth tail -/

/-- `sinh u ≤ u · e^u` for `u ≥ 0` (from `1 − 2u ≤ e^{−2u}`). -/
theorem sinh_le_self_mul_exp {u : ℝ} (hu : 0 ≤ u) : Real.sinh u ≤ u * Real.exp u := by
  have h := Real.add_one_le_exp (-(2 * u))
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos u).le
  have hprod : Real.exp u * Real.exp (-(2 * u)) = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  rw [hprod] at hmul
  rw [Real.sinh_eq]
  nlinarith [hmul]

theorem cothTail_eq_neg_cothPrim (w : ℝ) (hw : 0 < w) : cothTail w = -cothPrim w := by
  unfold cothTail cothPrim
  have hlt : Real.exp (-w) < 1 := exp_neg_lt_one hw
  rw [Real.log_div (by positivity) (by linarith)]
  ring

theorem cothTail_nonneg (w : ℝ) (hw : 0 < w) : 0 ≤ cothTail w := by
  unfold cothTail
  apply Real.log_nonneg
  have hlt : Real.exp (-w) < 1 := exp_neg_lt_one hw
  rw [le_div_iff₀ (by linarith)]
  linarith [Real.exp_pos (-w)]

/-- `cothTail w − cothTail c = ∫_{w}^{c} du / sinh u`. -/
theorem cothTail_sub (w c : ℝ) (hw : 0 < w) (hwc : w ≤ c) :
    cothTail w - cothTail c = ∫ u in w..c, 1 / Real.sinh u := by
  have hderiv : ∀ u ∈ Set.uIcc w c, HasDerivAt cothPrim (1 / Real.sinh u) u := by
    intro u hu
    rw [Set.uIcc_of_le hwc] at hu
    exact cothPrim_hasDerivAt (lt_of_lt_of_le hw hu.1)
  have hcont : ContinuousOn (fun u : ℝ => 1 / Real.sinh u) (Set.uIcc w c) := by
    rw [Set.uIcc_of_le hwc]
    apply continuousOn_const.div Real.continuous_sinh.continuousOn
    intro u hu
    exact ne_of_gt (sinh_pos_of_pos (lt_of_lt_of_le hw hu.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable),
    cothTail_eq_neg_cothPrim w hw, cothTail_eq_neg_cothPrim c (lt_of_lt_of_le hw hwc)]
  ring

/-- On `[w, c]` the integrand dominates `e^{-c} / u`, so the tail exceeds
`e^{-c} · log(c / w)`. -/
theorem cothTail_ge' (w c : ℝ) (hw : 0 < w) (hwc : w ≤ c) :
    Real.exp (-c) * (Real.log c - Real.log w) + cothTail c ≤ cothTail w := by
  have hc : 0 < c := lt_of_lt_of_le hw hwc
  have hsub := cothTail_sub w c hw hwc
  have hcont1 : ContinuousOn (fun u : ℝ => Real.exp (-c) * u⁻¹) (Set.uIcc w c) := by
    rw [Set.uIcc_of_le hwc]
    apply continuousOn_const.mul
    exact continuousOn_inv₀.mono (fun u hu => ne_of_gt (lt_of_lt_of_le hw hu.1))
  have hcont2 : ContinuousOn (fun u : ℝ => 1 / Real.sinh u) (Set.uIcc w c) := by
    rw [Set.uIcc_of_le hwc]
    apply continuousOn_const.div Real.continuous_sinh.continuousOn
    intro u hu
    exact ne_of_gt (sinh_pos_of_pos (lt_of_lt_of_le hw hu.1))
  have hmono : (∫ u in w..c, Real.exp (-c) * u⁻¹) ≤ ∫ u in w..c, 1 / Real.sinh u := by
    apply intervalIntegral.integral_mono_on hwc hcont1.intervalIntegrable hcont2.intervalIntegrable
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hw hu.1
    have hs : 0 < Real.sinh u := sinh_pos_of_pos hu0
    have hle : Real.sinh u ≤ u * Real.exp c :=
      (sinh_le_self_mul_exp hu0.le).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hu0.le)
    have hec : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
    rw [one_div, ← div_eq_mul_inv, div_le_iff₀ hu0]
    rw [show Real.exp (-c) = (Real.sinh u)⁻¹ * u * Real.exp (-c) * Real.sinh u / u by
      field_simp]
    have : (Real.sinh u)⁻¹ * Real.sinh u = 1 := inv_mul_cancel₀ (ne_of_gt hs)
    calc
      (Real.sinh u)⁻¹ * u * Real.exp (-c) * Real.sinh u / u
          = (Real.sinh u)⁻¹ * (Real.exp (-c) * Real.sinh u) := by field_simp
      _ ≤ (Real.sinh u)⁻¹ * (Real.exp (-c) * (u * Real.exp c)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le) (inv_pos.mpr hs).le
      _ = (Real.sinh u)⁻¹ * u := by
          rw [show Real.exp (-c) * (u * Real.exp c) = u * (Real.exp (-c) * Real.exp c) by ring,
            hec, mul_one]
  have heq : (∫ u in w..c, Real.exp (-c) * u⁻¹) = Real.exp (-c) * (Real.log c - Real.log w) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hw hc,
      Real.log_div (ne_of_gt hc) (ne_of_gt hw)]
  linarith [heq, hmono, hsub]

theorem cothTail_ge (w c : ℝ) (hw : 0 < w) (hwc : w ≤ c) :
    Real.exp (-c) * (Real.log c - Real.log w) ≤ cothTail w := by
  have := cothTail_ge' w c hw hwc
  linarith [cothTail_nonneg c (lt_of_lt_of_le hw hwc)]

/-- The repository's `1/32` tail constant, in `cothTail` form. -/
theorem cothTail_one_div_32 : 6 * Real.log 2 < cothTail (1 / 32) := by
  have := six_log_two_lt_integral_one_div_sinh_Ioi
  rw [integral_one_div_sinh_Ioi (by norm_num : (0 : ℝ) < 1 / 32)] at this
  exact this

/-- Sharper floor below `1/32`: `e^{-1/32} · log(1/(32 w)) + 6 log 2 ≤ cothTail w`. -/
theorem cothTail_ge_below_32 (w : ℝ) (hw : 0 < w) (hw32 : w ≤ 1 / 32) :
    Real.exp (-(1 / 32 : ℝ)) * (Real.log (1 / 32) - Real.log w) + 6 * Real.log 2 ≤ cothTail w := by
  have h := cothTail_ge' w (1 / 32) hw hw32
  linarith [cothTail_one_div_32]

/-- Dyadic form: half-width `2^{-m}` (window `2^{1-m}`), cutoff `1/8`. -/
theorem cothTail_dyadic (m : ℕ) (hm : 4 ≤ m) :
    Real.exp (-(1 / 8 : ℝ)) * (((m : ℝ) - 4) * Real.log 2) ≤
      cothTail (2 * (2 : ℝ) ^ (-(m : ℝ))) := by
  have hw : (0 : ℝ) < 2 * (2 : ℝ) ^ (-(m : ℝ)) := by positivity
  have h16 : (2 : ℝ) ^ (-(m : ℝ)) ≤ 1 / 16 := by
    have hle : (2 : ℝ) ^ (-(m : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (4 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h4 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h4] at hle
    exact hle
  have hwc : 2 * (2 : ℝ) ^ (-(m : ℝ)) ≤ 1 / 8 := by linarith
  have h := cothTail_ge _ (1 / 8) hw hwc
  have hlog : Real.log (1 / 8) - Real.log (2 * (2 : ℝ) ^ (-(m : ℝ))) =
      ((m : ℝ) - 4) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by norm_num),
      show (1 / 8 : ℝ) = 2 ^ (-(3 : ℝ)) by
        rw [Real.rpow_neg (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num,
      Real.log_rpow (by norm_num)]
    ring
  rw [hlog] at h
  exact h

end AEGIS.RHDyadicDiagonalV13

#print axioms AEGIS.RHDyadicDiagonalV13.diagonal_lower
#print axioms AEGIS.RHDyadicDiagonalV13.diagonal_lower_recovers_103_over_100
#print axioms AEGIS.RHDyadicDiagonalV13.cothTail_ge
#print axioms AEGIS.RHDyadicDiagonalV13.cothTail_dyadic
#print axioms AEGIS.RHDyadicDiagonalV13.cothTail_ge_below_32
