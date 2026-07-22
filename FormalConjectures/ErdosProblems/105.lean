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
# Erdős Problem 105

*References:*
- [erdosproblems.com/105](https://www.erdosproblems.com/105)
- [Be83] Beck, József, *On the lattice property of the plane and some problems of Dirac, Motzkin
  and Erdős in combinatorial geometry*. Combinatorica (1983), 281-297.
- [ErPu95] Erdős, P. and Purdy, G., *Two combinatorial problems in the plane*. Discrete Comput.
  Geom. (1995), 441-443.
- [SzTr83] Szemerédi, Endre and Trotter, Jr., William T., *Extremal problems in discrete
  geometry*. Combinatorica (1983), 381-392.
-/

open EuclideanGeometry

namespace Erdos105

/--
Let $A,B\subset \mathbb{R}^2$ be disjoint sets of size $n$ and $n-3$ respectively, with not all
of $A$ contained on a single line. Is there a line which contains at least two points from $A$
and no points from $B$?

This has been disproved by Xichuan in the comments, who has found three explicit
counterexamples.
-/
@[category research solved, AMS 5 52]
theorem erdos_105 : answer(False) ↔
    ∀ A B : Finset ℝ², Disjoint A B → A.card = B.card + 3 →
      ¬ Collinear ℝ (A : Set ℝ²) →
      ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q] := by
  sorry

/--
A construction of Hickerson shows that this fails with $n-2$.
-/
@[category research solved, AMS 5 52]
theorem erdos_105.variants.hickerson : ¬ ∀ A B : Finset ℝ², Disjoint A B →
    A.card = B.card + 2 → ¬ Collinear ℝ (A : Set ℝ²) →
    ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q] := by
  sorry

/--
A result independently proved by Beck [Be83] and Szemerédi and Trotter [SzTr83] (see [211])
implies it is true with $n-3$ replaced by $cn$ for some constant $c>0$.
-/
@[category research solved, AMS 5 52]
theorem erdos_105.variants.beck_szemerediTrotter : ∃ c > (0 : ℝ),
    ∀ A B : Finset ℝ², Disjoint A B → (B.card : ℝ) ≤ c * A.card →
      ¬ Collinear ℝ (A : Set ℝ²) →
      ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q] := by
  sorry

/--
It remains possible that this holds with $n-4$ (or in general with $n-O(1)$ or $(1-o(1))n$).
-/
@[category research open, AMS 5 52]
theorem erdos_105.variants.sub_four : answer(sorry) ↔
    ∀ A B : Finset ℝ², Disjoint A B → A.card = B.card + 4 →
      ¬ Collinear ℝ (A : Set ℝ²) →
      ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q] := by
  sorry

end Erdos105
