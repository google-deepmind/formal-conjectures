import WeilArchFiniteQuadraticV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
AEGIS Ω — continuous weighted Archimedean Gram integral v1.

This module performs exactly one new step beyond the fixed-T finite Gram
positivity already proved in `WeilArchFiniteQuadraticV1`: integration of a
nonnegative spectral weight over an ordered finite T-interval.

The spectral weight is intentionally abstract.  In particular, this file does
NOT assert that the actual zeta Archimedean weight
`Re (digamma (1/4 + iT/2)) - log π` is nonnegative, and it does NOT identify
this weighted integral with the complete Archimedean term of the Weil operator.
Those remain separate analytic/semantic obligations.

No finite Galerkin PSD promotion, formula-to-Weil operator identity, global
Weil positivity, RH, repository admission, merge, or authority effect follows.
-/

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- Continuous weighted integral of the already-defined fixed-T finite
Archimedean sine-source quadratic. -/
def WeilArchWeightedTailQuadraticV1
    (I : Finset ℤ) (L A B : ℝ) (u : ℤ → ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ T in A..B, w T * WeilArchFiniteQuadraticV1 I L T u

/-- A nonnegative spectral weight preserves the fixed-T Gram positivity under
interval integration, provided every point of the interval is nonresonant on
the finite band. -/
theorem weil_arch_weighted_tail_quadratic_nonnegative_v1
    (I : Finset ℤ) (L A B : ℝ) (u : ℤ → ℝ) (w : ℝ → ℝ)
    (hAB : A ≤ B)
    (hL : 0 < L)
    (hw : ∀ T ∈ Set.Icc A B, 0 ≤ w T)
    (hden : ∀ T ∈ Set.Icc A B, ∀ n ∈ I,
      T ^ 2 - (WeilArchRhoV1 L * (n : ℝ)) ^ 2 ≠ 0) :
    0 ≤ WeilArchWeightedTailQuadraticV1 I L A B u w := by
  unfold WeilArchWeightedTailQuadraticV1
  apply intervalIntegral.integral_nonneg hAB
  intro T hT
  exact mul_nonneg
    (hw T hT)
    (weil_arch_finite_quadratic_nonnegative_v1
      I L T u hL (fun n hn => hden T hT n hn))

#print axioms weil_arch_weighted_tail_quadratic_nonnegative_v1
