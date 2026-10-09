import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
AEGIS Ω — conservative Weil/Bombieri criterion domain v1.

Source boundary: Enrico Bombieri's official Clay Mathematics Institute problem
description, Section 5 (printed pp. 121–122), is used only to pin the mathematical
shape of the explicit formula and Weil negativity route.

This file formalizes a compact-smooth positive-half-line subdomain, not Weil's full
class W. It defines the two zero-moment conditions, the autocorrelation shape, and
the right-hand side of the explicit formula using Mathlib primitives.

It proves neither the explicit formula nor the Riemann Hypothesis, and it does not
assert that negativity on this restricted subdomain is equivalent to RH.

FULL_WEIL_CLASS_COVERAGE_OPEN
EXPLICIT_FORMULA_THEOREM_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set
open Complex
open MeasureTheory
open scoped ContDiff

noncomputable section

/-- A conservative smooth compactly-supported subdomain on the positive half-line.
    This is intentionally narrower than Bombieri's full class W. -/
def WeilCompactSmoothGV1 :=
  { g : ℝ → ℂ // ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Set.Ioi 0 }

/-- The two vanishing moments appearing in the Weil criterion route. -/
def WeilMomentConditionsV1 (g : WeilCompactSmoothGV1) : Prop :=
  (∫ x in Set.Ioi (0 : ℝ), g.1 x / (x : ℂ)) = 0 ∧
  (∫ x in Set.Ioi (0 : ℝ), g.1 x) = 0

/-- Multiplicative autocorrelation shape used in Bombieri's statement. -/
def WeilAutocorrelationV1 (g : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), g.1 (x * y) * star (g.1 y)

/-- One positive-integer prime-power term of the explicit-formula right side.
    Index `n` represents the positive integer `n + 1`. -/
def WeilPrimeTermV1 (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  let m : ℕ := n + 1
  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
    (f (m : ℝ) + (1 / (m : ℂ)) * f (((m : ℝ))⁻¹))

/-- Prime-power sum from the explicit-formula right side. -/
def WeilPrimeSumV1 (f : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, WeilPrimeTermV1 f n

/-- Archimedean integrand from the explicit-formula right side. -/
def WeilArchimedeanIntegrandV1 (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (f x + (1 / (x : ℂ)) * f (x⁻¹) - (2 / (x : ℂ)) * f 1) /
    ((x : ℂ) - ((x⁻¹ : ℝ) : ℂ))

/-- The constant multiplying `f(1)` in Bombieri's normalization. -/
def WeilArchimedeanConstantV1 : ℂ :=
  ((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ)

/-- Archimedean integral from `1` to `∞`, represented as a set integral on `(1,∞)`. -/
def WeilArchimedeanIntegralV1 (f : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), WeilArchimedeanIntegrandV1 f x

/-- Concrete right-hand-side expression from the explicit formula. -/
def WeilExplicitRightSideV1 (f : ℝ → ℂ) : ℂ :=
  WeilPrimeSumV1 f + WeilArchimedeanConstantV1 * f 1 + WeilArchimedeanIntegralV1 f

/-- Convergence obligations kept explicit because `tsum` and integrals are totalized in Lean. -/
def WeilExplicitRightSideConvergentV1 (f : ℝ → ℂ) : Prop :=
  Summable (WeilPrimeTermV1 f) ∧
  IntegrableOn (WeilArchimedeanIntegrandV1 f) (Set.Ioi (1 : ℝ))

/-- Negativity candidate on the restricted compact-smooth domain only.
    Reality of the value is included explicitly rather than assumed. -/
def WeilCompactSmoothNegativityV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    WeilExplicitRightSideConvergentV1 (WeilAutocorrelationV1 g) →
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).im = 0 ∧
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0

#check WeilCompactSmoothGV1
#check WeilMomentConditionsV1
#check WeilAutocorrelationV1
#check WeilPrimeTermV1
#check WeilExplicitRightSideV1
#check WeilCompactSmoothNegativityV1
