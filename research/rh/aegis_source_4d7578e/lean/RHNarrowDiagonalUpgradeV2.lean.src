import WeilSeparatedArchBridgeV31
import Mathlib.Tactic

/-!
AEGIS Omega -- narrower-support diagonal upgrade V2.

For total log-support width 1/64, the interval (1/64,1/32] is already
outside the autocorrelation support. Its actual transformed Archimedean
integrand is at most -16 E. The interval has length 1/64 and therefore
contributes at most -E/4, improving the inherited 103/100 lower bound to
32/25. This is a narrower test class, NOT a replacement for the width-1/32
class and NOT an assertion that the existing gNarrow has this support.
This candidate source requires pinned Lean replay and an axiom audit.
-/

open Set MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowDiagonalUpgradeV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilMixedAlgebraV2

def WidthOneSixtyFourAt (g : WeilCompactSmoothGV1) (a : ℝ) : Prop :=
  LogSupportIn g (a - 1 / 128) (a + 1 / 128)

theorem narrow_implies_retained_v2 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) : WidthOneThirtyTwoAt g a := by
  intro t ht
  have h := hw ht
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem narrow_autocorrelation_zero_v2 (g : WeilCompactSmoothGV1) (a u : ℝ)
    (hw : WidthOneSixtyFourAt g a) (hu : (1 / 64 : ℝ) < u) :
    WeilAutocorrelationV1 g (Real.exp u) = 0 := by
  have hc := logCross_zero_outside g g
    (a - 1 / 128) (a + 1 / 128) (a - 1 / 128) (a + 1 / 128)
    u hw hw (Or.inr (by linarith))
  rw [logCross_eq_mixed_v28] at hc
  have hm := (mul_eq_zero.mp hc).resolve_left (by simp)
  change WeilAutocorrelationV1 g (Real.exp u) = 0 at hm
  exact hm

/-- Elementary upper bound from the inherited exponential constant; no
numerical approximation of the transcendental function is used. -/
theorem sinh_small_upper_v2 (u : ℝ) (hu : u ≤ (1 / 32 : ℝ)) :
    Real.sinh u ≤ (1 / 16 : ℝ) := by
  have he : Real.exp u ≤ (16 / 15 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : u ≤ (1 / 16 : ℝ))).trans
      exp_one_over_16_upper.le
  have hn : (31 / 32 : ℝ) ≤ Real.exp (-u) := by
    linarith [Real.add_one_le_exp (-u)]
  rw [Real.sinh_eq]
  linarith

theorem narrow_middle_pointwise_v2 (g : WeilCompactSmoothGV1) (a u : ℝ)
    (hw : WidthOneSixtyFourAt g a)
    (hu : u ∈ Ioc (1 / 64 : ℝ) (1 / 32 : ℝ)) :
    widthArchLogIntegrandV26 g u ≤ -16 * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hp : 0 < Real.sinh u :=
    AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos (by linarith [hu.1])
  have hs := sinh_small_upper_v2 u hu.2
  have hm := mul_le_mul_of_nonneg_left hs hE
  unfold widthArchLogIntegrandV26
  rw [narrow_autocorrelation_zero_v2 g a u hw hu.1]
  simp only [Complex.zero_re, mul_zero, zero_sub]
  apply (div_le_iff₀ hp).2
  nlinarith

theorem narrow_inner_integral_upgrade_v2 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ), widthArchLogIntegrandV26 g u) ≤
      energy g.1 * diagonalSmallV21 - (1 / 4 : ℝ) * energy g.1 := by
  let C : ℝ := energy g.1 * (Real.exp (1 / 64 : ℝ) / 2)
  have hE := energy_nonnegative g.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfull := width_arch_log_integrableOn_v27 g
  have hl : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (0 : ℝ) (1 / 64 : ℝ)) :=
    hfull.mono_set (fun _ hu => hu.1)
  have hr : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc (1 / 64 : ℝ) (1 / 32 : ℝ)) :=
    hfull.mono_set (by intro u hu; change 0 < u; linarith [hu.1])
  have hleft : (∫ u in Ioc (0 : ℝ) (1 / 64 : ℝ), widthArchLogIntegrandV26 g u) ≤
      (1 / 64 : ℝ) * C := by
    calc
      _ ≤ ∫ _u in Ioc (0 : ℝ) (1 / 64 : ℝ), C := by
        apply setIntegral_mono_on hl continuous_const.integrableOn_Ioc measurableSet_Ioc
        intro u hu
        exact width_arch_log_inner_pointwise_v26 g hu.1 (by linarith [hu.2])
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul,
          Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 64)]
        ring
  have hright : (∫ u in Ioc (1 / 64 : ℝ) (1 / 32 : ℝ), widthArchLogIntegrandV26 g u) ≤
      -(1 / 4 : ℝ) * energy g.1 := by
    calc
      _ ≤ ∫ _u in Ioc (1 / 64 : ℝ) (1 / 32 : ℝ), -16 * energy g.1 := by
        apply setIntegral_mono_on hr continuous_const.integrableOn_Ioc measurableSet_Ioc
        intro u hu
        exact narrow_middle_pointwise_v2 g a u hw hu
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul,
          Real.volume_real_Ioc_of_le (by norm_num : (1 / 64 : ℝ) ≤ 1 / 32)]
        ring
  have hu : Ioc (0 : ℝ) (1 / 64 : ℝ) ∪ Ioc (1 / 64 : ℝ) (1 / 32 : ℝ) =
      Ioc (0 : ℝ) (1 / 32 : ℝ) := by
    ext u
    constructor
    · rintro (h | h)
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
    · intro h
      by_cases hsplit : u ≤ (1 / 64 : ℝ)
      · exact Or.inl ⟨h.1, hsplit⟩
      · exact Or.inr ⟨lt_of_not_ge hsplit, h.2⟩
  have hd : Disjoint (Ioc (0 : ℝ) (1 / 64 : ℝ)) (Ioc (1 / 64 : ℝ) (1 / 32 : ℝ)) := by
    rw [Set.disjoint_left]
    intro u h1 h2
    linarith [h1.2, h2.1]
  rw [← hu, setIntegral_union hd measurableSet_Ioc hl hr]
  calc
    _ ≤ (1 / 64 : ℝ) * C - (1 / 4 : ℝ) * energy g.1 := by linarith
    _ ≤ (1 / 32 : ℝ) * C - (1 / 4 : ℝ) * energy g.1 := by nlinarith
    _ = _ := by dsimp [C, diagonalSmallV21]; ring

theorem narrow_arch_budget_upgrade_v2 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (diagonalSmallV21 - diagonalTailV24) - (1 / 4 : ℝ) * energy g.1 := by
  rw [archimedean_real_eq_log_integral_v27, width_arch_log_split_v27,
    width_arch_tail_integral_eq_v27 g a (narrow_implies_retained_v2 g a hw)]
  have hi := narrow_inner_integral_upgrade_v2 g a hw
  linarith

theorem narrow_diagonal_32_over_25_v2 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    (32 / 25 : ℝ) * energy g.1 ≤ -(B g g).re := by
  have hp := width_diagonal_prime_sum_zero_v24 g a (narrow_implies_retained_v2 g a hw)
  have hE := energy_nonnegative g.1
  have hf : (103 / 100 : ℝ) ≤ diagonalTailV24 - diagonalKappaV21 - diagonalSmallV21 := by
    have ht := diagonal_tail_gt_six_log_two_v24
    have hc := diagonal_constant_floor
    have hn := certificate_diagonal_threshold
    unfold diagonalKappaV21 diagonalSmallV21
    linarith
  have hm := mul_le_mul_of_nonneg_left hf hE
  have hb := narrow_arch_budget_upgrade_v2 g a hw
  rw [actual_diagonal_rhs_decomposition g hp]
  nlinarith

end AEGIS.RHNarrowDiagonalUpgradeV2

#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_implies_retained_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_autocorrelation_zero_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.sinh_small_upper_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_middle_pointwise_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_inner_integral_upgrade_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_arch_budget_upgrade_v2
#print axioms AEGIS.RHNarrowDiagonalUpgradeV2.narrow_diagonal_32_over_25_v2
