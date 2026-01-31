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
# Green's Open Problem 77: Heilbronn Triangle Problem

*Reference:* [Ben Green's problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)

Given $n$ points in the unit square, what is the smallest possible area of a triangle 
formed by three of them? The conjecture is that $h(n) = O(n^{-c})$ for some $c$ with $1 < c < 2$.
-/

open EuclideanSpace

namespace Green77

/--
Any $n$ points in the unit square contain a triangle with area $\le h(n)$ 
for some function $h$.
-/
@[category research open, AMS 52 05]
theorem heilbronn_triangle_problem (n : ℕ) : ∃ (h : ℕ → ℝ),
  (∀ points : Set (ℝ × ℝ),
    (∀ p ∈ points, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) →
    (Set.ncard points = n) →
    ∃ (p₁ p₂ p₃ : ℝ × ℝ), p₁ ∈ points ∧ p₂ ∈ points ∧ p₃ ∈ points ∧
      p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
      |p₁.1 * (p₂.2 - p₃.2) + p₂.1 * (p₃.2 - p₁.2) + p₃.1 * (p₁.2 - p₂.2)| / 2 ≤ h n) := by
  sorry

end Green77
