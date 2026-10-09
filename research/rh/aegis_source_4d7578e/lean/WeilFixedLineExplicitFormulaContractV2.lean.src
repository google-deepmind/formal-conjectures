import ZeroCountingMellinSummabilityV1
import WeilPrimeLineIdentityV1
import WeilAutocorrelationPoleAggregationV1
import WeilPoleTermV1

/-!
AEGIS Ω — corrected fixed-line integration contract for the RH explicit-formula lane.

The adopted #490 proof is a paired-Hadamard / Fubini argument on a fixed line
`c > 1`.  It does not move a rectangle across the critical strip and therefore
has no horizontal-segment-vanishing obligation.

This module binds four already proved surfaces to the actual autocorrelation:
* multiplicity-safe absolute zero summability from #488;
* compact-smooth autocorrelation closure and RHS convergence from #493;
* the fixed-line von-Mangoldt prime identity from #490;
* endpoint aggregation from #507, together with the zeta pole theorem ported
  to the same Lean/Mathlib pin.

It is a readiness/integration theorem only.  It does NOT prove the remaining
paired-Hadamard whole explicit-formula identity, the arithmetic sign, global
Weil positivity, or RH.
-/

open Set Filter Topology MeasureTheory Complex

set_option autoImplicit false

noncomputable section

/-- The actual autocorrelation inherits the multiplicity-weighted absolutely
convergent nontrivial-zero series from the compact-smooth closure theorem. -/
theorem weil_autocorrelation_zero_residue_summable_v2 (g : WeilCompactSmoothGV1) :
    Summable (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g)) := by
  change Summable
    (WeilZeroIndexSummandV1 (WeilAutocorrelationCompactSmoothV1 g).1)
  exact weil_compact_smooth_zero_summable_v1 (WeilAutocorrelationCompactSmoothV1 g)

/-- Absolute norm summability is retained, so this is stronger than merely
choosing a symmetric-height summation prescription. -/
theorem weil_autocorrelation_zero_residue_norm_summable_v2 (g : WeilCompactSmoothGV1) :
    Summable (fun rho => ‖WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho‖) := by
  change Summable
    (fun rho => ‖WeilZeroIndexSummandV1 (WeilAutocorrelationCompactSmoothV1 g).1 rho‖)
  exact weil_compact_smooth_zero_norm_summable_v1 (WeilAutocorrelationCompactSmoothV1 g)

/-- The existing fixed-line prime identity applies directly to the actual
autocorrelation after #493 repackages it in the compact-smooth class. -/
theorem weil_autocorrelation_prime_line_identity_v2
    (g : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) *
          mellin (WeilAutocorrelationV1 g) ((c : ℂ) + t * I)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        WeilAutocorrelationV1 g (n : ℝ) := by
  change (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
          riemannZeta ((c : ℂ) + t * I)) *
          mellin (WeilAutocorrelationCompactSmoothV1 g).1 ((c : ℂ) + t * I)) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        (WeilAutocorrelationCompactSmoothV1 g).1 (n : ℝ)
  exact weil_compact_smooth_prime_line_identity_v1
    (WeilAutocorrelationCompactSmoothV1 g) c hc

/-- The finite collection of kernel-proved prerequisites that the fixed-line
paired-Hadamard assembly may consume.  Deliberately absent: any moving-contour
or horizontal-segment hypothesis. -/
structure WeilAutocorrelationFixedLineReadinessV2 (g : WeilCompactSmoothGV1) : Prop where
  zero_side_summable :
    Summable (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g))
  zero_side_norm_summable :
    Summable (fun rho => ‖WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho‖)
  rhs_convergent :
    WeilExplicitRightSideConvergentV1 (WeilAutocorrelationV1 g)
  endpoint_pole_aggregate :
    mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 =
      WeilEndpointPoleAggregateV1 (mellin g.1 0) (mellin g.1 1)
  prime_line_identity :
    ∀ (c : ℝ), 1 < c →
      (1 / (2 * Real.pi) : ℝ) •
          (∫ t : ℝ, (-deriv riemannZeta ((c : ℂ) + t * I) /
            riemannZeta ((c : ℂ) + t * I)) *
            mellin (WeilAutocorrelationV1 g) ((c : ℂ) + t * I)) =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          WeilAutocorrelationV1 g (n : ℝ)

/-- All corrected fixed-line prerequisites are already theorem consequences on
this carrier; no contour-shift assumption is introduced. -/
theorem weil_autocorrelation_fixed_line_readiness_v2
    (g : WeilCompactSmoothGV1) : WeilAutocorrelationFixedLineReadinessV2 g := by
  refine ⟨
    weil_autocorrelation_zero_residue_summable_v2 g,
    weil_autocorrelation_zero_residue_norm_summable_v2 g,
    weil_autocorrelation_explicit_right_side_convergent_v1 g,
    weil_autocorrelation_pole_term_eq_endpoint_aggregate_v1 g,
    ?_⟩
  intro c hc
  exact weil_autocorrelation_prime_line_identity_v2 g c hc

/-- With the repository's two moment conditions, the same readiness package is
available and the actual autocorrelation pole aggregate vanishes. -/
theorem weil_autocorrelation_fixed_line_readiness_of_moments_v2
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    WeilAutocorrelationFixedLineReadinessV2 g ∧
      mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 = 0 := by
  exact ⟨weil_autocorrelation_fixed_line_readiness_v2 g,
    weil_moment_conditions_autocorrelation_pole_term_zero_v1 g hm⟩

#print axioms weil_autocorrelation_zero_residue_summable_v2
#print axioms weil_autocorrelation_zero_residue_norm_summable_v2
#print axioms weil_autocorrelation_prime_line_identity_v2
#print axioms weil_autocorrelation_fixed_line_readiness_v2
#print axioms weil_autocorrelation_fixed_line_readiness_of_moments_v2
