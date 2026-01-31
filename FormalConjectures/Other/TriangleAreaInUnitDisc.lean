/-
Copyright 2025 The Formal Conjectures Authors.

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
# Triangle Area in Unit Disc

Given $n$ points in the unit disc, must there always be a triangle with area at most $n^{-2} + o(1)$?
-/

namespace TriangleAreaInUnitDisc

open EuclideanSpace

/--
For any $n$ points in the unit disc, there exists a triangle with area $\le C n^{-2}$.
-/
@[category research open, AMS 52 05]
theorem triangle_area_bound (n : ℕ) : ∃ C > (0 : ℝ),
  ∀ (points : Set (ℝ × ℝ)),
    (∀ p ∈ points, p.1 ^ 2 + p.2 ^ 2 ≤ 1) →
    (Set.ncard points = n) →
    ∃ (p₁ p₂ p₃ : ℝ × ℝ), p₁ ∈ points ∧ p₂ ∈ points ∧ p₃ ∈ points ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
    |p₁.1 * (p₂.2 - p₃.2) + p₂.1 * (p₃.2 - p₁.2) + p₃.1 * (p₁.2 - p₂.2)| / 2 ≤ C / n ^ 2 := by
  sorry

end TriangleAreaInUnitDisc
