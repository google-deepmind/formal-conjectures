import WeilAutocorrelationMellinFactorV10
import WeilMomentZeroDetectionV10
import ZeroHeightSummabilityBridgeV1
import Mathlib.Tactic

/-!
AEGIS Ω — actual zero-summand witness V10.

The spectral detector and autocorrelation Mellin factorization now meet on the
repository's canonical zero functional.

For every nontrivial zeta zero rho, there exists a compact-smooth packet g
satisfying the two repository moment conditions such that the actual
multiplicity-weighted summand

  WeilZeroIndexSummandV1 (Autocorrelation g) rho

is nonzero.

This is an unconditional witness-construction theorem; it does not assume rho
is off the critical line and it does not assert a sign.

AUTHORITY_EFFECT = NONE.
-/

open Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilActualZeroSummandWitnessV10

open AEGIS.WeilAutocorrelationMellinFactorV10
open AEGIS.WeilMomentZeroDetectionV10

theorem exists_moment_zero_packet_with_nonzero_actual_zero_summand_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho ≠ 0 := by
  obtain ⟨g, hm, hcoeff⟩ :=
    exists_nonzero_zero_pair_coefficient_v10 rho
  refine ⟨g, hm, ?_⟩
  unfold WeilZeroIndexSummandV1
  rw [mellin_autocorrelation_factor_v10 g rho.1]
  exact hcoeff

/-- Pointwise identification of the actual zero summand with the paired
Mellin coefficient. -/
theorem actual_zero_summand_eq_paired_mellin_v10
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho =
      (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
        (mellin g.1 rho.1 *
          conj (mellin g.1 (1 - conj rho.1))) := by
  unfold WeilZeroIndexSummandV1
  rw [mellin_autocorrelation_factor_v10 g rho.1]

end AEGIS.WeilActualZeroSummandWitnessV10

#print axioms AEGIS.WeilActualZeroSummandWitnessV10.exists_moment_zero_packet_with_nonzero_actual_zero_summand_v10
#print axioms AEGIS.WeilActualZeroSummandWitnessV10.actual_zero_summand_eq_paired_mellin_v10
