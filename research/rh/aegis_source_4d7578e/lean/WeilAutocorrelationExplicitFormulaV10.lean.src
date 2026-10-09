import WeilExplicitFormulaV10
import RHFinalClosureSpineV1
import WeilAutocorrelationClosureV1
import WeilAutocorrelationPoleAggregationV1
import WeilAutocorrelationRealityV1
import Mathlib.Tactic

/-!
AEGIS Ω — autocorrelation specialization of the whole explicit formula V10.

For a compact-smooth g satisfying the repository's two Mellin moment
conditions, the endpoint pole term of its multiplicative autocorrelation
vanishes.  The whole explicit formula therefore becomes

  WeilExplicitRightSideV1 (Autocorrelation g)
    = - sum_rho m_rho M(Autocorrelation g)(rho).

This is the exact arithmetic/zero-side quadratic identity needed by the final
sign problem.  No sign is inferred here.

AUTHORITY_EFFECT = NONE.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilAutocorrelationExplicitFormulaV10

open AEGIS.WeilExplicitFormulaV10

/-- Whole explicit formula specialized to the actual autocorrelation carrier. -/
theorem autocorrelation_explicit_formula_v10
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    WeilExplicitRightSideV1 (WeilAutocorrelationV1 g) =
      - (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) := by
  have hEF :=
    weil_compact_smooth_explicit_formula_v1
      (WeilAutocorrelationCompactSmoothV1 g)
  have hpole :=
    weil_moment_conditions_autocorrelation_pole_term_zero_v1 g hm
  change
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho) =
      mellin (WeilAutocorrelationV1 g) 0 +
        mellin (WeilAutocorrelationV1 g) 1 -
        WeilExplicitRightSideV1 (WeilAutocorrelationV1 g) at hEF
  rw [hpole, zero_sub] at hEF
  exact neg_eq_iff_eq_neg.mp hEF.symm

/-- The final arithmetic sign is exactly nonnegativity of the real part of
the canonical zero quadratic. -/
theorem autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 ↔
      0 ≤
        (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  rw [autocorrelation_explicit_formula_v10 g hm]
  simp

/-- Repository final-sign residual rewritten with no arithmetic expression
left: it is precisely universal nonnegativity of the canonical zero
quadratic on the moment-zero compact-smooth class. -/
theorem final_sign_residual_iff_zero_quadratic_nonnegative_v10 :
    AEGIS.RHFinalClosureV1.FinalSignResidualV1 ↔
      ∀ g : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 g →
        0 ≤
          (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  unfold AEGIS.RHFinalClosureV1.FinalSignResidualV1
  constructor
  · intro h g hm
    exact
      (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        g hm).mp (h g hm)
  · intro h g hm
    exact
      (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        g hm).mpr (h g hm)

end AEGIS.WeilAutocorrelationExplicitFormulaV10

#print axioms AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
#print axioms AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
#print axioms AEGIS.WeilAutocorrelationExplicitFormulaV10.final_sign_residual_iff_zero_quadratic_nonnegative_v10
