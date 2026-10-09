import WeilZeroTranslationV11
import WeilAutocorrelationExplicitFormulaV10
import RHRestrictedWeilBridgeV13
import Mathlib.Tactic

/-!
AEGIS Ω — RH implies the final Weil sign residual, V13.

This is the converse of `RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13`.

The route is purely algebraic on top of the already-kernelized V11 Mellin
factorization of the multiplicative autocorrelation:

  M(Autocorrelation g)(s) = M(g)(s) * conj(M(g)(1 - conj s)).

On the critical line `Re s = 1/2` one has `1 - conj s = s`, so the right
side is `M(g)(s) * conj(M(g)(s)) = ‖M(g)(s)‖²`.  Under Mathlib's
`RiemannHypothesis` every nontrivial zeta zero lies on that line, hence every
multiplicity-weighted zero summand of the autocorrelation quadratic is a
nonnegative real.  Absolute summability already exists in the repository, so
the canonical zero quadratic is nonnegative, and the V10 whole
explicit-formula bridge yields `FinalSignResidualV1`.

Together with the V13 forward bridge this closes the equivalence

  RiemannHypothesis ↔ UniversalZeroQuadraticNonnegativeV10
  RiemannHypothesis ↔ MillenniumMomentReachedV10.

This is a criterion, i.e. an equivalence.  It does not decide either side.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilRHImpliesFinalSignV13

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1
open AEGIS.RHMillenniumGateV10
open AEGIS.RHRestrictedWeilBridgeV13

/-- On the critical line the Mellin reflection point is the point itself. -/
theorem one_sub_conj_of_re_half_v13 {s : ℂ} (hs : s.re = 1 / 2) :
    1 - conj s = s := by
  apply Complex.ext
  · simp only [sub_re, one_re, conj_re, hs]
    norm_num
  · simp

/-- Under RH every nontrivial zero lies on the critical line. -/
theorem zero_re_half_of_rh_v13 (hRH : RiemannHypothesis)
    (rho : RiemannNontrivialZeroIndexV2) : rho.1.re = 1 / 2 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hrho1 : rho.1 ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  exact hRH rho.1 rho.2.1 rho.2.2 hrho1

/-- Under RH every canonical zero summand of the autocorrelation quadratic
is a multiplicity times a modulus square. -/
theorem rh_zero_summand_eq_normSq_v13 (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1) (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho =
      ((analyticOrderNatAt riemannZeta rho.1 : ℝ) *
        Complex.normSq (mellin g.1 rho.1) : ℝ) := by
  rw [autocorrelation_zero_summand_factorization_v11,
    one_sub_conj_of_re_half_v13 (zero_re_half_of_rh_v13 hRH rho),
    Complex.mul_conj]
  push_cast
  ring

/-- Under RH every canonical zero summand has nonnegative real part. -/
theorem rh_zero_summand_nonnegative_v13 (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1) (rho : RiemannNontrivialZeroIndexV2) :
    0 ≤ (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  rw [rh_zero_summand_eq_normSq_v13 hRH g rho, Complex.ofReal_re]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- RH makes the entire canonical autocorrelation zero quadratic
nonnegative. -/
theorem rh_zero_quadratic_nonnegative_v13 (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1) :
    0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hsum :
      Summable (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g)) :=
    weil_compact_smooth_zero_summable_v1
      (WeilAutocorrelationCompactSmoothV1 g)
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg (fun rho => rh_zero_summand_nonnegative_v13 hRH g rho)

/-- Mathlib RH implies the repository final sign residual. -/
theorem rh_implies_final_sign_residual_v13 (hRH : RiemannHypothesis) :
    FinalSignResidualV1 := by
  rw [final_sign_residual_iff_zero_quadratic_nonnegative_v10]
  intro g _
  exact rh_zero_quadratic_nonnegative_v13 hRH g

/-- Mathlib RH implies the universal zero-quadratic nonnegativity. -/
theorem rh_implies_universal_v13 (hRH : RiemannHypothesis) :
    UniversalZeroQuadraticNonnegativeV10 :=
  universal_zero_quadratic_iff_final_sign_v10.mpr
    (rh_implies_final_sign_residual_v13 hRH)

/-- The restricted Weil criterion, both directions kernel-checked. -/
theorem rh_iff_final_sign_v13 :
    RiemannHypothesis ↔ FinalSignResidualV1 :=
  ⟨rh_implies_final_sign_residual_v13, final_sign_implies_rh_v13⟩

/-- The restricted Weil criterion in the universal zero-quadratic form. -/
theorem rh_iff_universal_v13 :
    RiemannHypothesis ↔ UniversalZeroQuadraticNonnegativeV10 :=
  ⟨rh_implies_universal_v13,
    restricted_weil_criterion_kernel_bridge_v13⟩

/-- The repository millennium gate is exactly Mathlib RH. -/
theorem millennium_moment_iff_rh_v13 :
    MillenniumMomentReachedV10 ↔ RiemannHypothesis :=
  millennium_moment_iff_universal_v13.trans rh_iff_universal_v13.symm

end AEGIS.WeilRHImpliesFinalSignV13

#print axioms AEGIS.WeilRHImpliesFinalSignV13.rh_zero_summand_eq_normSq_v13
#print axioms AEGIS.WeilRHImpliesFinalSignV13.rh_implies_final_sign_residual_v13
#print axioms AEGIS.WeilRHImpliesFinalSignV13.rh_iff_final_sign_v13
#print axioms AEGIS.WeilRHImpliesFinalSignV13.rh_iff_universal_v13
#print axioms AEGIS.WeilRHImpliesFinalSignV13.millennium_moment_iff_rh_v13
