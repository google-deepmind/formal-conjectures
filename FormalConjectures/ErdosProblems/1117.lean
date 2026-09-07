/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1117

*References:*
- [erdosproblems.com/1117](https://www.erdosproblems.com/1117)
- [Ha74] Hayman, W. K., Research problems in function theory: new problems (1974), 155–180.
- [HePi68] Herzog, F. and Piranian, G., The counting function for points of maximum modulus
  (1968), 240–243.
- [GlPa24] Glücksam, A. and Pardo-Simón, L., An approximate solution to Erdős' maximum
  modulus points problem. J. Math. Anal. Appl. (2024), Paper No. 127768.
- [Gu26] Gu, Q., A negative answer to a question of Erdős on maximum modulus points.
  https://github.com/FireflySentinel/erdos-1117
-/

open Set Complex Filter
open scoped Topology

namespace Erdos1117

/-- A function which is not a constant multiple of a nonnegative integer power. -/
def IsNonMonomial (f : ℂ → ℂ) : Prop :=
  ¬ ∃ (c : ℂ) (m : ℕ), ∀ z, f z = c * z ^ m

/-- The number of maximum modulus points on the circle of radius `r`. -/
noncomputable def maximumCount (f : ℂ → ℂ) (r : ℝ) : ℕ∞ :=
  {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}.encard

/-- The product/common-value fibre for the actual logarithmic derivative. -/
def commonValueFibre (f : ℂ → ℂ) (s a : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 * p.2 = s ∧ p.1 * deriv f p.1 / f p.1 = a ∧
    starRingEnd ℂ ((starRingEnd ℂ p.2) * deriv f (starRingEnd ℂ p.2) /
      f (starRingEnd ℂ p.2)) = a}

/-- Image values relevant to the maximum modulus argument. -/
def commonValueImage (f : ℂ → ℂ) : Set (ℂ × ℂ) :=
  {y | y.1 ≠ 0 ∧ y.2 ≠ (analyticOrderNatAt f 0 : ℂ) ∧ y.2 ≠ 0 ∧
    (commonValueFibre f y.1 y.2).Nonempty}

/-- Local finiteness relative to the image, rather than at the excluded base values. -/
def LocallyFiniteExceptions (f : ℂ → ℂ) (T : Set (ℂ × ℂ)) : Prop :=
  ∀ y ∈ commonValueImage f, ∃ U ∈ 𝓝 y, (T ∩ U).Finite

/--
The regular-image claim of [Gu26, Proposition 4.2]: outside a countable,
locally finite set, the total fibre cardinality is locally constant.
-/
@[category research open, AMS 30 32]
theorem fibreDegreeConstancy :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ T : Set (ℂ × ℂ), T.Countable ∧ LocallyFiniteExceptions f T ∧
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) := by
  sorry

/--
The small-product claim of [Gu26, Lemma 3.1 and Proposition 4.2]: every
regular image component meets arbitrarily small nonzero products.
-/
@[category research open, AMS 30 32]
theorem smallProductsOnComponents :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∀ T : Set (ℂ × ℂ), T.Countable → LocallyFiniteExceptions f T →
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) →
        ∀ η : ℝ, 0 < η → ∀ x : ↥(commonValueImage f \ T),
          ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2 := by
  sorry

/--
Let $f(z)$ be an entire function which is not a monomial. Let $\nu(r)$ count the
number of $z$ with $\lvert z\rvert=r$ such that
$\lvert f(z)\rvert=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.
(This is a finite quantity if $f$ is not a monomial.)

Is it possible for $\limsup \nu(r)=\infty$?

This is Problem 2.16 in [Ha74], where it is attributed to Erdős.
The answer to the first question is yes, as shown by Herzog and Piranian [HePi68].
-/
@[category research solved, AMS 30]
theorem erdos_1117.parts.i :
    answer(True) ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ IsNonMonomial f ∧
      ∀ N : ℕ, ∃ᶠ r : ℝ in atTop, (N : ℕ∞) ≤ maximumCount f r := by
  sorry

/--
Is it possible for $\liminf \nu(r)=\infty$?

The second question is still open, although an 'approximate' affirmative answer
is given by Glücksam and Pardo-Simón [GlPa24].
-/
@[category research open, AMS 30]
theorem erdos_1117.parts.ii :
    answer(sorry) ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ IsNonMonomial f ∧
      ∀ N : ℕ, ∀ᶠ r : ℝ in atTop, (N : ℕ∞) ≤ maximumCount f r := by
  sorry

/--
The two component claims in [Gu26] imply a negative answer to the second question.
-/
@[category research solved, AMS 30 32,
  conditional formal_proof using lean4 at
    "https://github.com/FireflySentinel/erdos-1117/blob/0fe62c8c850346d6ad3ba5c43f12c5b644791e49/checks/FormalConjecturesBridge.lean#L57"
  assuming fibreDegreeConstancy smallProductsOnComponents]
theorem erdos_1117.variants.negative_of_component_data
    (hdegree : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ T : Set (ℂ × ℂ), T.Countable ∧ LocallyFiniteExceptions f T ∧
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard))
    (hsmall : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∀ T : Set (ℂ × ℂ), T.Countable → LocallyFiniteExceptions f T →
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) →
        ∀ η : ℝ, 0 < η → ∀ x : ↥(commonValueImage f \ T),
          ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2) :
    False ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ IsNonMonomial f ∧
      ∀ N : ℕ, ∀ᶠ r : ℝ in atTop, (N : ℕ∞) ≤ maximumCount f r := by
  sorry

/--
Under the same two analytic inputs, the maximum-point count is bounded outside a
countable set of positive radii [Gu26, Theorem 1.1].
-/
@[category research solved, AMS 30 32,
  conditional formal_proof using lean4 at
    "https://github.com/FireflySentinel/erdos-1117/blob/0fe62c8c850346d6ad3ba5c43f12c5b644791e49/checks/FormalConjecturesBridge.lean#L33"
  assuming fibreDegreeConstancy smallProductsOnComponents]
theorem erdos_1117.variants.countable_exceptions
    (hdegree : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ T : Set (ℂ × ℂ), T.Countable ∧ LocallyFiniteExceptions f T ∧
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard))
    (hsmall : ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∀ T : Set (ℂ × ℂ), T.Countable → LocallyFiniteExceptions f T →
        IsLocallyConstant (fun y : ↥(commonValueImage f \ T) =>
          (commonValueFibre f y.1.1 y.1.2).encard) →
        ∀ η : ℝ, 0 < η → ∀ x : ↥(commonValueImage f \ T),
          ∃ y ∈ connectedComponent x, ‖y.1.1‖ < η ^ 2) :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → IsNonMonomial f →
      ∃ k : ℕ, 0 < k ∧ ∃ E : Set ℝ, E.Countable ∧ E ⊆ Ioi 0 ∧
        ∀ r : ℝ, 0 < r → r ∉ E → maximumCount f r ≤ 2 * k := by
  sorry

end Erdos1117
