import WeilThreeBlockPrimeEvaluationV30
import WeilThreeBlockNormBridgeV21

/-!
Conditional assembly over the actual repository integrals.
The original three-bound interface is retained. Translation invariance reduces
the strengthened interface to two Archimedean bounds. Moment cancellation of
the separated rank-one kernel is proved below; its connection to the complete
Archimedean integral and the two quantitative bounds remain obligations.
-/
open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilThreeBlockCrossAssemblyV30
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeWindowV29
open AEGIS.WeilThreeBlockPrimeEvaluationV30
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilThreeBlockNormBridgeV21
open AEGIS.WeilWidthArchIntegralV27

theorem adjacent_rational_arch_margin :
    (75 / 9086 : ℝ) < 1 / 100 := by norm_num

theorem outer_rational_arch_margin :
    (15 / 13216 : ℝ) < 1 / 100 := by norm_num

private theorem mixed_bound_of_prime_and_arch
    (p q : WeilCompactSmoothGV1) (E c k : ℝ)
    (hE : 0 ≤ E) (hc : 0 ≤ c) (hck : c ≤ k)
    (hzero : mixed p q 1 = 0)
    (hprime : WeilPrimeSumV1 (mixed p q) = ((c * E : ℝ) : ℂ))
    (harch : ‖WeilArchimedeanIntegralV1 (mixed p q)‖ ≤ (1 / 100 : ℝ) * E) :
    ‖B p q‖ ≤ (k + 1 / 100) * E := by
  have hp : ‖WeilPrimeSumV1 (mixed p q)‖ = c * E := by
    rw [hprime, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hE)]
  unfold B WeilExplicitRightSideV1
  rw [hzero, mul_zero, add_zero]
  calc
    ‖WeilPrimeSumV1 (mixed p q) + WeilArchimedeanIntegralV1 (mixed p q)‖
        ≤ ‖WeilPrimeSumV1 (mixed p q)‖ + ‖WeilArchimedeanIntegralV1 (mixed p q)‖ := norm_add_le _ _
    _ ≤ c * E + (1 / 100 : ℝ) * E := by rw [hp]; exact add_le_add (le_refl _) harch
    _ ≤ (k + 1 / 100) * E := by nlinarith [mul_le_mul_of_nonneg_right hck hE]

theorem three_cross_bounds_of_arch
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (harch01 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch02 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch12 : ‖WeilArchimedeanIntegralV1 (mixed (gZero g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1) :
    ‖B (gMinus g) (gZero g)‖ ≤ (51 / 100 : ℝ) * energy g.1 ∧
    ‖B (gMinus g) (gPlus g)‖ ≤ (9 / 25 : ℝ) * energy g.1 ∧
    ‖B (gZero g) (gPlus g)‖ ≤ (51 / 100 : ℝ) * energy g.1 := by
  have hE := energy_nonnegative g.1
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h01zero : mixed (gMinus g) (gZero g) 1 = 0 := by
    simpa using adjacent_mixed_nat_zero_v29 g a hw 1 (by norm_num)
  have h02zero : mixed (gMinus g) (gPlus g) 1 = 0 := by
    simpa using outer_mixed_nat_zero_v29 g a hw 1 (by norm_num)
  have h12zero : mixed (gZero g) (gPlus g) 1 = 0 := by
    rw [adjacent_mixed_shift_eq g 1 (by norm_num)]
    exact h01zero
  constructor
  · convert mixed_bound_of_prime_and_arch (gMinus g) (gZero g) (energy g.1)
      (Real.log 2 / Real.sqrt 2) (1 / 2) hE
      (div_nonneg hlog (Real.sqrt_nonneg _)) prime_adjacent_scalar_upper.le
      h01zero (adjacent_prime_sum_exact g a hw) harch01 using 1 <;> norm_num
  constructor
  · convert mixed_bound_of_prime_and_arch (gMinus g) (gPlus g) (energy g.1)
      (Real.log 2 / 2) (7 / 20) hE (div_nonneg hlog (by norm_num))
      prime_outer_scalar_upper.le h02zero (outer_prime_sum_exact g a hw) harch02
      using 1 <;> norm_num
  · convert mixed_bound_of_prime_and_arch (gZero g) (gPlus g) (energy g.1)
      (Real.log 2 / Real.sqrt 2) (1 / 2) hE
      (div_nonneg hlog (Real.sqrt_nonneg _)) prime_adjacent_scalar_upper.le
      h12zero (right_adjacent_prime_sum_exact g a hw) harch12 using 1 <;> norm_num

theorem three_block_bound_of_arch
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (z0 z1 z2 : ℂ)
    (harch01 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch02 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch12 : ‖WeilArchimedeanIntegralV1 (mixed (gZero g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 (gMinus g) (gZero g) (gPlus g)))).re ≤
      -(1 / 10 : ℝ) * energy (combo z0 z1 z2 (gMinus g) (gZero g) (gPlus g)).1 := by
  obtain ⟨hd01, hd02, hd12⟩ := three_blocks_pairwise_disjoint g a hw
  obtain ⟨he0, he1, he2⟩ := three_blocks_energy g
  obtain ⟨hb01, hb02, hb12⟩ := three_cross_bounds_of_arch g a hw harch01 harch02 harch12
  have hw0 := translate_logSupportIn g (-Real.log 2) _ _ hw
  have hw1 := translate_logSupportIn g 0 _ _ hw
  have hw2 := translate_logSupportIn g (Real.log 2) _ _ hw
  have h0 : WidthOneThirtyTwoAt (gMinus g) (a - Real.log 2) := by
    change LogSupportIn (translatePacket g (-Real.log 2))
      (a - Real.log 2 - 1 / 64) (a - Real.log 2 + 1 / 64)
    convert hw0 using 1 <;> ring
  have h1 : WidthOneThirtyTwoAt (gZero g) a := by
    simpa [WidthOneThirtyTwoAt, gZero] using hw1
  have h2 : WidthOneThirtyTwoAt (gPlus g) (a + Real.log 2) := by
    change LogSupportIn (translatePacket g (Real.log 2))
      (a + Real.log 2 - 1 / 64) (a + Real.log 2 + 1 / 64)
    convert hw2 using 1 <;> ring
  have hl01 : l2 (gMinus g).1 * l2 (gZero g).1 = energy g.1 := by
    rw [l2, l2, he0, he1, ← pow_two, Real.sq_sqrt (energy_nonnegative g.1)]
  have hl02 : l2 (gMinus g).1 * l2 (gPlus g).1 = energy g.1 := by
    rw [l2, l2, he0, he2, ← pow_two, Real.sq_sqrt (energy_nonnegative g.1)]
  have hl12 : l2 (gZero g).1 * l2 (gPlus g).1 = energy g.1 := by
    rw [l2, l2, he1, he2, ← pow_two, Real.sq_sqrt (energy_nonnegative g.1)]
  apply actual_three_block_l2_bound z0 z1 z2 (gMinus g) (gZero g) (gPlus g)
      hd01 hd02 hd12
  · simpa [square_l2] using width_diagonal_103_over_100_v27 (gMinus g) _ h0
  · simpa [square_l2] using width_diagonal_103_over_100_v27 (gZero g) _ h1
  · simpa [square_l2] using width_diagonal_103_over_100_v27 (gPlus g) _ h2
  · simpa only [mul_assoc, hl01] using hb01
  · simpa only [mul_assoc, hl02] using hb02
  · simpa only [mul_assoc, hl12] using hb12

/-- Both adjacent Archimedean integrals are exactly equal, without a width or
moment hypothesis. -/
theorem adjacent_arch_integral_eq (g : WeilCompactSmoothGV1) :
    WeilArchimedeanIntegralV1 (mixed (gZero g) (gPlus g)) =
      WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g)) := by
  unfold WeilArchimedeanIntegralV1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hpos : 0 < x := lt_trans (by norm_num) hx
  simp only [WeilArchimedeanIntegrandV1,
    adjacent_mixed_shift_eq g x hpos,
    adjacent_mixed_shift_eq g (x⁻¹) (inv_pos.mpr hpos),
    adjacent_mixed_shift_eq g 1 (by norm_num)]

/-- Only the adjacent and outer estimates are independent obligations. -/
theorem three_cross_bounds_of_two_arch
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (harch01 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch02 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1) :
    ‖B (gMinus g) (gZero g)‖ ≤ (51 / 100 : ℝ) * energy g.1 ∧
    ‖B (gMinus g) (gPlus g)‖ ≤ (9 / 25 : ℝ) * energy g.1 ∧
    ‖B (gZero g) (gPlus g)‖ ≤ (51 / 100 : ℝ) * energy g.1 := by
  exact three_cross_bounds_of_arch g a hw harch01 harch02
    (by simpa only [adjacent_arch_integral_eq] using harch01)

theorem three_block_bound_of_two_arch
    (g : WeilCompactSmoothGV1) (a : ℝ) (hw : WidthOneThirtyTwoAt g a)
    (z0 z1 z2 : ℂ)
    (harch01 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gZero g))‖ ≤
      (1 / 100 : ℝ) * energy g.1)
    (harch02 : ‖WeilArchimedeanIntegralV1 (mixed (gMinus g) (gPlus g))‖ ≤
      (1 / 100 : ℝ) * energy g.1) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 (gMinus g) (gZero g) (gPlus g)))).re ≤
      -(1 / 10 : ℝ) * energy (combo z0 z1 z2 (gMinus g) (gZero g) (gPlus g)).1 := by
  exact three_block_bound_of_arch g a hw z0 z1 z2 harch01 harch02
    (by simpa only [adjacent_arch_integral_eq] using harch01)

/-- Subtract the moment-cancelled term directly; no infinite series is needed. -/
theorem arch_kernel_sub_rank_one (v : ℝ) (hv : 0 < v) :
    Real.exp (-v / 2) / (1 - Real.exp (-2 * v)) - Real.exp (-v / 2) =
      Real.exp (-5 * v / 2) / (1 - Real.exp (-2 * v)) := by
  have he : Real.exp (-2 * v) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd : 1 - Real.exp (-2 * v) ≠ 0 := ne_of_gt (sub_pos.mpr he)
  have hm : Real.exp (-v / 2) * Real.exp (-2 * v) = Real.exp (-5 * v / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (eq_div_iff hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd]
  nlinarith [hm]

/-- The separated leading exponential term vanishes by the repository's
minus moment. This is an iterated-integral identity, not yet the change of
variables/Fubini identification with the actual Archimedean integral. -/
theorem arch_rank_one_moment_zero
    (p q : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 p) :
    (∫ s : ℝ, ∫ t : ℝ,
      ((Real.exp (-s / 2) : ℂ) *
        AEGIS.WeilLogCoordinateIsometryV21.logLift p.1 s) *
      ((Real.exp (t / 2) : ℂ) *
        conj (AEGIS.WeilLogCoordinateIsometryV21.logLift q.1 t))) = 0 := by
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  change logMomentMinus p * _ = 0
  rw [logMomentMinus_eq_repository, hm.1, zero_mul]

/-- The rank-one cancellation in the actual difference-kernel normalization. -/
theorem arch_exp_difference_moment_zero
    (p q : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 p) :
    (∫ s : ℝ, ∫ t : ℝ,
      (Real.exp (-(s - t) / 2) : ℂ) *
        AEGIS.WeilLogCoordinateIsometryV21.logLift p.1 s *
        conj (AEGIS.WeilLogCoordinateIsometryV21.logLift q.1 t)) = 0 := by
  rw [← arch_rank_one_moment_zero p q hm]
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [] with t
  have he : Real.exp (-(s - t) / 2) = Real.exp (-s / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Complex.ofReal_mul]
  ring

/-- On a separated support, the remainder kernel is bounded by its value at
the minimal positive separation. -/
theorem arch_remainder_le_at_gap (δ v : ℝ) (hδ : 0 < δ) (hv : δ ≤ v) :
    Real.exp (-5 * v / 2) / (1 - Real.exp (-2 * v)) ≤
      Real.exp (-5 * δ / 2) / (1 - Real.exp (-2 * δ)) := by
  have hn : Real.exp (-5 * v / 2) ≤ Real.exp (-5 * δ / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-2 * v) ≤ Real.exp (-2 * δ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : 0 < 1 - Real.exp (-2 * δ) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hpv : 0 < 1 - Real.exp (-2 * v) := lt_of_lt_of_le hp (by linarith)
  apply (div_le_div_iff₀ hpv hp).mpr
  exact (mul_le_mul_of_nonneg_right hn hp.le).trans
    (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos (-5 * δ / 2)).le)

end AEGIS.WeilThreeBlockCrossAssemblyV30

#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.three_cross_bounds_of_arch
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.three_block_bound_of_arch
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.adjacent_arch_integral_eq
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.three_cross_bounds_of_two_arch
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.three_block_bound_of_two_arch
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.arch_kernel_sub_rank_one
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.arch_rank_one_moment_zero
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.arch_exp_difference_moment_zero
#print axioms AEGIS.WeilThreeBlockCrossAssemblyV30.arch_remainder_le_at_gap
