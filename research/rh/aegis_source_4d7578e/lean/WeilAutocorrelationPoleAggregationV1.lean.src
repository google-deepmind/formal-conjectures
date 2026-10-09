import WeilMellinInversionV1
import WeilAutocorrelationClosureV1
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
AEGIS Ω — Mellin endpoint aggregation for the Weil autocorrelation lane.

This module transfers the two-profile aggregation / information-loss pattern
to the two Mellin endpoints of the repository's Lebesgue-measure Weil
autocorrelation.

For endpoint values `a,b : ℂ`, the pole cross-aggregate

  a * conj b + b * conj a

is exactly twice the real part of one cross term. Hence the aggregate loses
the complementary imaginary information: aggregate zero does not force
`a = 0` and `b = 0` separately.

The second layer kernel-binds this algebra to the actual autocorrelation. The
`s = 1` endpoint is proved by compact-support Fubini and the pinned Mathlib
Mellin scaling theorem. The `s = 0` endpoint is transported through the
already verified reciprocal involution for the unchanged `dy` autocorrelation.

No global sign inequality, RH equivalence, admission, or authority effect is
asserted here.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

/-- One oriented endpoint cross term. -/
def WeilEndpointCrossTermV1 (a b : ℂ) : ℂ :=
  a * conj b

/-- Symmetric endpoint aggregate. -/
def WeilEndpointPoleAggregateV1 (a b : ℂ) : ℂ :=
  WeilEndpointCrossTermV1 a b + WeilEndpointCrossTermV1 b a

/-- Swapping the two endpoint profiles conjugates the oriented cross term. -/
theorem weil_endpoint_cross_swap_eq_conj_v1 (a b : ℂ) :
    WeilEndpointCrossTermV1 b a = conj (WeilEndpointCrossTermV1 a b) := by
  simp [WeilEndpointCrossTermV1, mul_comm]

/-- The symmetric aggregate remembers only twice the real part of one cross
term. This is the precise lossy projection. -/
theorem weil_endpoint_pole_aggregate_eq_two_re_v1 (a b : ℂ) :
    WeilEndpointPoleAggregateV1 a b =
      (((2 : ℝ) * (WeilEndpointCrossTermV1 a b).re : ℝ) : ℂ) := by
  rw [WeilEndpointPoleAggregateV1, weil_endpoint_cross_swap_eq_conj_v1]
  apply Complex.ext <;> simp <;> ring

/-- If both endpoint profiles vanish, then their pole aggregate vanishes. -/
theorem weil_endpoint_pole_aggregate_zero_of_endpoints_zero_v1
    {a b : ℂ} (ha : a = 0) (hb : b = 0) :
    WeilEndpointPoleAggregateV1 a b = 0 := by
  simp [ha, hb, WeilEndpointPoleAggregateV1, WeilEndpointCrossTermV1]

/-- Concrete collision: two nonzero endpoint profiles can have zero aggregate. -/
theorem weil_endpoint_pole_aggregate_zero_collision_v1 :
    WeilEndpointPoleAggregateV1 (1 : ℂ) Complex.I = 0 := by
  simp [WeilEndpointPoleAggregateV1, WeilEndpointCrossTermV1]

/-- Therefore aggregate zero cannot recover the two endpoint profiles. -/
theorem weil_endpoint_pole_aggregate_zero_not_force_zero_profiles_v1 :
    ∃ a b : ℂ,
      a ≠ 0 ∧ b ≠ 0 ∧ WeilEndpointPoleAggregateV1 a b = 0 := by
  refine ⟨1, Complex.I, ?_, ?_, weil_endpoint_pole_aggregate_zero_collision_v1⟩
  · norm_num
  · simp

/-- The repository's first zero-moment integral is exactly the Mellin endpoint
at `s = 0`. -/
theorem weil_mellin_zero_eq_moment0_v1 (g : WeilCompactSmoothGV1) :
    mellin g.1 0 =
      ∫ x in Ioi (0 : ℝ), g.1 x / (x : ℂ) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp [Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]

/-- The repository's second zero-moment integral is exactly the Mellin endpoint
at `s = 1`. -/
theorem weil_mellin_one_eq_moment1_v1 (g : WeilCompactSmoothGV1) :
    mellin g.1 1 =
      ∫ x in Ioi (0 : ℝ), g.1 x := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp

/-- The existing two-moment condition is a sufficient (but, by the collision
above, algebraically non-minimal) condition for vanishing endpoint aggregate. -/
theorem weil_moment_conditions_endpoint_pole_aggregate_zero_v1
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    WeilEndpointPoleAggregateV1 (mellin g.1 0) (mellin g.1 1) = 0 := by
  rcases hm with ⟨hm0, hm1⟩
  have h0 : mellin g.1 0 = 0 :=
    (weil_mellin_zero_eq_moment0_v1 g).trans hm0
  have h1 : mellin g.1 1 = 0 :=
    (weil_mellin_one_eq_moment1_v1 g).trans hm1
  exact weil_endpoint_pole_aggregate_zero_of_endpoints_zero_v1 h0 h1

/-- Joint integrand used for the compact-support Fubini step. -/
private def WeilAutocorrelationJointV1 (g : WeilCompactSmoothGV1) (x y : ℝ) : ℂ :=
  g.1 (x * y) * conj (g.1 y)

private theorem weil_autocorrelation_joint_continuous_v1 (g : WeilCompactSmoothGV1) :
    Continuous (Function.uncurry (WeilAutocorrelationJointV1 g)) := by
  exact (g.2.1.continuous.comp (continuous_fst.mul continuous_snd)).mul
    (continuous_star.comp (g.2.1.continuous.comp continuous_snd))

private theorem weil_autocorrelation_joint_tsupport_subset_v1
    (g : WeilCompactSmoothGV1) :
    tsupport (Function.uncurry (WeilAutocorrelationJointV1 g)) ⊆
      WeilAutocorrelationSupportEnvelopeV1 g ×ˢ tsupport g.1 := by
  apply closure_minimal ?_
    ((weil_autocorrelation_support_envelope_compact_v1 g).prod g.2.2.1).isClosed
  intro p hp
  have hy : g.1 p.2 ≠ 0 := by
    intro h
    apply hp
    change g.1 (p.1 * p.2) * conj (g.1 p.2) = 0
    rw [h, map_zero, mul_zero]
  have hxy : g.1 (p.1 * p.2) ≠ 0 := by
    intro h
    apply hp
    change g.1 (p.1 * p.2) * conj (g.1 p.2) = 0
    rw [h, zero_mul]
  have hyK : p.2 ∈ tsupport g.1 := subset_tsupport g.1 hy
  have hxyK : p.1 * p.2 ∈ tsupport g.1 := subset_tsupport g.1 hxy
  refine ⟨?_, hyK⟩
  refine ⟨(p.1 * p.2, p.2), ⟨hxyK, hyK⟩, ?_⟩
  exact mul_div_cancel_right₀ p.1 (ne_of_gt (g.2.2.2 hyK))

private theorem weil_autocorrelation_joint_hasCompactSupport_v1
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (Function.uncurry (WeilAutocorrelationJointV1 g)) :=
  ((weil_autocorrelation_support_envelope_compact_v1 g).prod g.2.2.1).of_isClosed_subset
    (isClosed_tsupport _) (weil_autocorrelation_joint_tsupport_subset_v1 g)

private theorem weil_autocorrelation_joint_swap_v1 (g : WeilCompactSmoothGV1) :
    (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), WeilAutocorrelationJointV1 g x y) =
      ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), WeilAutocorrelationJointV1 g x y := by
  exact integral_integral_swap_of_hasCompactSupport
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioi (0 : ℝ)))
    (weil_autocorrelation_joint_continuous_v1 g)
    (weil_autocorrelation_joint_hasCompactSupport_v1 g)

/-- The `s = 1` Mellin endpoint of the actual autocorrelation factors into
the two endpoint profiles. -/
theorem weil_autocorrelation_mellin_one_factor_v1 (g : WeilCompactSmoothGV1) :
    mellin (WeilAutocorrelationV1 g) 1 =
      mellin g.1 1 * conj (mellin g.1 0) := by
  rw [mellin]
  simp only [sub_self, cpow_zero, one_smul]
  change (∫ x in Ioi (0 : ℝ),
      ∫ y in Ioi (0 : ℝ), WeilAutocorrelationJointV1 g x y) = _
  rw [weil_autocorrelation_joint_swap_v1 g]
  calc
    (∫ y in Ioi (0 : ℝ),
        ∫ x in Ioi (0 : ℝ), WeilAutocorrelationJointV1 g x y) =
        ∫ y in Ioi (0 : ℝ),
          (∫ x in Ioi (0 : ℝ), g.1 (x * y)) * conj (g.1 y) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            change (∫ x in Ioi (0 : ℝ), g.1 (x * y) * conj (g.1 y)) =
              (∫ x in Ioi (0 : ℝ), g.1 (x * y)) * conj (g.1 y)
            rw [integral_mul_const]
    _ = ∫ y in Ioi (0 : ℝ),
          (((y : ℂ)⁻¹ * mellin g.1 1) * conj (g.1 y)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            have hscale :
                (∫ x in Ioi (0 : ℝ), g.1 (x * y)) =
                  (y : ℂ)⁻¹ * mellin g.1 1 := by
              have h := mellin_comp_mul_right g.1 (1 : ℂ) hy
              simpa [mellin, Complex.cpow_neg_one] using h
            change (∫ x in Ioi (0 : ℝ), g.1 (x * y)) * conj (g.1 y) =
              ((y : ℂ)⁻¹ * mellin g.1 1) * conj (g.1 y)
            rw [hscale]
    _ = mellin g.1 1 *
          (∫ y in Ioi (0 : ℝ), (y : ℂ)⁻¹ * conj (g.1 y)) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            ring
    _ = mellin g.1 1 * conj (mellin g.1 0) := by
            congr 1
            rw [weil_mellin_zero_eq_moment0_v1 g, ← integral_conj]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            simp [div_eq_mul_inv, mul_comm]

/-- The reciprocal involution of the unchanged `dy` autocorrelation exchanges
the two Mellin endpoints by complex conjugation. -/
theorem weil_autocorrelation_mellin_zero_eq_conj_one_v1
    (g : WeilCompactSmoothGV1) :
    mellin (WeilAutocorrelationV1 g) 0 =
      conj (mellin (WeilAutocorrelationV1 g) 1) := by
  have hinv := mellin_comp_inv (WeilAutocorrelationV1 g) (0 : ℂ)
  simp only [neg_zero] at hinv
  rw [← hinv]
  unfold mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [zero_sub, sub_self, cpow_zero, one_smul,
    Complex.cpow_neg_one, smul_eq_mul]
  rw [weil_autocorrelation_reciprocal_v1 g hx]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  simp [hxC]

/-- The `s = 0` endpoint is the conjugate orientation of the same cross term. -/
theorem weil_autocorrelation_mellin_zero_factor_v1 (g : WeilCompactSmoothGV1) :
    mellin (WeilAutocorrelationV1 g) 0 =
      mellin g.1 0 * conj (mellin g.1 1) := by
  rw [weil_autocorrelation_mellin_zero_eq_conj_one_v1,
    weil_autocorrelation_mellin_one_factor_v1]
  simp [mul_comm]

/-- The actual autocorrelation pole term is exactly the symmetric endpoint
aggregate. -/
theorem weil_autocorrelation_pole_term_eq_endpoint_aggregate_v1
    (g : WeilCompactSmoothGV1) :
    mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 =
      WeilEndpointPoleAggregateV1 (mellin g.1 0) (mellin g.1 1) := by
  rw [weil_autocorrelation_mellin_zero_factor_v1,
    weil_autocorrelation_mellin_one_factor_v1]
  rfl

/-- Therefore the actual pole term sees only twice the real part of one
endpoint cross term. -/
theorem weil_autocorrelation_pole_term_eq_two_re_v1 (g : WeilCompactSmoothGV1) :
    mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 =
      (((2 : ℝ) *
        (WeilEndpointCrossTermV1 (mellin g.1 0) (mellin g.1 1)).re : ℝ) : ℂ) := by
  rw [weil_autocorrelation_pole_term_eq_endpoint_aggregate_v1,
    weil_endpoint_pole_aggregate_eq_two_re_v1]

/-- The legacy two-zero-moment condition kills the actual autocorrelation pole
term. This proves sufficiency only; the collision theorem above shows that the
endpoint pair is not recoverable from the aggregate. -/
theorem weil_moment_conditions_autocorrelation_pole_term_zero_v1
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 = 0 := by
  rw [weil_autocorrelation_pole_term_eq_endpoint_aggregate_v1]
  exact weil_moment_conditions_endpoint_pole_aggregate_zero_v1 g hm

end
