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

open Filter Metric

/-!
# Ben Green's Open Problem 77

*Reference:* [Ben Green's Open Problem 77](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.77)
-/

namespace Green77

/-- The closed unit disc in ℝ², i.e., all points at distance at most 1 from the origin. -/
def unitDisc : Set (ℝ × ℝ) := {p | dist p (0, 0) ≤ 1}

/-- Compute the area of a triangle with vertices p₁, p₂, p₃ using the shoelace formula. -/
noncomputable def triangleArea (p₁ p₂ p₃ : ℝ × ℝ) : ℝ :=
  (1/2) * |p₁.1 * (p₂.2 - p₃.2) + p₂.1 * (p₃.2 - p₁.2) + p₃.1 * (p₁.2 - p₂.2)|

/--
Given $n$ points in the unit disc, must there be a triangle determined by these points with area
at most $n^{-2 + o(1)}$?

Komlós, Pintz, and Szemerédi showed that the $o(1)$ term is necessary, and proved that there must
exist a triangle with area at most $n^{-8/7}$.
-/
@[category research open, AMS 52 05]
theorem green_77 :
    answer(sorry) ↔ ∃ (f : ℕ → ℝ), (atTop.Tendsto f (𝓝 0)) ∧
      ∃ N, ∀ n ≥ N, ∀ (S : Finset (ℝ × ℝ)),
        (∀ p ∈ S, p ∈ unitDisc) →
        S.card = n →
        ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S,
          p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
          triangleArea p₁ p₂ p₃ ≤ (n : ℝ)^(-2 : ℝ) * (1 + f n) := by
  sorry

end Green77
