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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 96

*Is every set Λ ⊂ ℤ either a Sidon set, or a set of analyticity?*

A set Λ ⊂ ℤ is called a *set of analyticity* if every continuous function f : 𝕋 → ℂ whose
Fourier coefficients are supported on Λ is analytic. This is formalized as the Fourier coefficients
decaying exponentially.

*Reference:*
- [Gr24] [Ben Green's Open Problem 96](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.96)
-/

open Set MeasureTheory Real Complex

namespace Green96

/--
A set `Λ ⊂ ℤ` is a *set of analyticity* if every continuous function `f : 𝕋 → ℂ` whose
Fourier coefficients are supported on `Λ` extends to an analytic function.
This is formalized as the Fourier coefficients decaying exponentially.
-/
def IsSetOfAnalyticity (Λ : Set ℤ) : Prop :=
  ∀ f : ℝ → ℂ, Continuous f →
    (∀ x, f (x + 2 * Real.pi) = f x) →
    (∀ n : ℤ, n ∉ Λ → ∫ x in Icc 0 (2 * Real.pi), f x * Complex.exp (-Complex.I * n * x) = 0) →
    ∃ C a, a > 0 ∧ ∀ n : ℤ,
      norm (∫ x in Icc 0 (2 * Real.pi), f x * Complex.exp (-Complex.I * n * x)) ≤
      C * Real.exp (-a * (n.natAbs : ℝ))

/--
Is every set `Λ ⊂ ℤ` either a Sidon set, or a set of analyticity?
-/
@[category research open, AMS 11 43]
theorem green_96 :
    answer(sorry) ↔ ∀ Λ : Set ℤ, IsSidon Λ ∨ IsSetOfAnalyticity Λ := by
  sorry

end Green96
