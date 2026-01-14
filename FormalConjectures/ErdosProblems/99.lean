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
# Erdős Problem 99

*References:*
* [erdosproblems.com/99](https://www.erdosproblems.com/99)
* [BeFo99] Bezdek, Andr\'{a}s and Fodor, Ferenc, Minimal diameter of certain sets in the plane. J. Combin. Theory Ser. A (1999), 105-111.
* [Er94b] Erd\H{o}s, Paul, Some problems in number theory, combinatorics and combinatorial geometry. Math. Pannon. (1994), 261-269.
-/
open Set Metric EuclideanGeometry

namespace Erdos99

/-- A set has minimum distance 1 if all pairwise distances are at least 1, and the minimum is achieved. -/
def HasMinDist1 (A : Finset ℝ²) : Prop :=
  (∀ᵉ (p ∈ A) (q ∈ A), p ≠ q → dist p q ≥ 1) ∧
  (∃ᵉ (p ∈ A) (q ∈ A), dist p q = 1)

/-- Three points form an equilateral triangle of side length 1. -/
def FormsEquilateralTriangle (p q r : ℝ²) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1

/-- For sufficiently large n, any set of n points with minimum distance 1 that minimizes diameter must contain an equilateral triangle of side length 1. -/
@[category research open, AMS 52]
theorem erdos_99 :
    answer(sorry) ↔ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ²,
      (A.card = n ∧ HasMinDist1 A ∧
       ∀ B : Finset ℝ², B.card = n → HasMinDist1 B →
         diam (A : Set ℝ²) ≤ diam (B : Set ℝ²)) →
      ∃ᵉ (p ∈ A) (q ∈ A) (r ∈ A), FormsEquilateralTriangle p q r := by
sorry

end Erdos99
