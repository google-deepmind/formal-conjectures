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
# Erdős Problem 100
*Reference:* [erdosproblems.com/100](https://www.erdosproblems.com/100)
-/

open scoped EuclideanGeometry
open Metric

/--
A set of points in ℝ² satisfies the distance constraints if all pairwise distances are at least 1
and if two distinct distances differ then they differ by at least 1.
-/
def ValidDistanceSet (A : Finset ℝ²) : Prop :=
  A.toSet.Pairwise (fun p q => 1 ≤ dist p q) ∧
  (A ×ˢ A).toSet.Pairwise (fun ⟨p₁, q₁⟩ ⟨p₂, q₂⟩ =>
    dist p₁ q₁ ≠ dist p₂ q₂ → 1 ≤ |dist p₁ q₁ - dist p₂ q₂|)

@[category test]
example : diam (∅ : Finset ℝ²) = 0 := by
  simp [diam]

/--
Let $A$ be a set of $n$ points in $\mathbb{R}^2$ such that all pairwise distances are at least $1$
and if two distinct distances differ then they differ by at least $1$.
Is the diameter of $A ≫ n$?
-/
@[category research open, AMS 51]
theorem erdos_100 : ∃ C > 0, ∀ (n : ℕ) (A : Finset ℝ²),
    A.card = n → ValidDistanceSet A → C * n ≤ diam A := by
  sorry

/--
A stronger conjecture: perhaps the diameter is even ≥ n - 1 for sufficiently large n.
This would give a linear bound rather than just a "much greater than" relationship.
-/
@[category research open, AMS 52]
theorem erdos_100_stronger : ∀ᶠ n in Filter.atTop, ∀ (A : Finset ℝ²),
    A.card = n → ValidDistanceSet A → n - 1 ≤ diam A := by
  sorry
