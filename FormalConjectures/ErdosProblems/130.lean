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
# Erdős Problem 130

*Reference:* [erdosproblems.com/130](https://www.erdosproblems.com/130)

Related to [Problem 213](https://www.erdosproblems.com/213).

Let $A \subseteq \mathbb{R}^2$ be an infinite set with no three collinear and no four concyclic
points. Can the integer-distance graph on $A$ (adjacent iff at integer distance) have infinite
chromatic number?

[Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_,
Discrete Mathematics (1997), 227-231.

[AnEr45] Anning, N.H. and Erdős, P., _Integral distances_, Bull. Amer. Math. Soc. (1945),
598-600.
-/

open SimpleGraph EuclideanGeometry

namespace Erdos130

/-- A point set $A \subseteq \mathbb{R}^2$ is in Erdős general position if no three distinct
points of $A$ are collinear, and no four distinct points of $A$ are concyclic. -/
def ErdosGeneralPosition (A : Set ℝ²) : Prop :=
  NonTrilinear A ∧
  (∀ Q : Set ℝ², Q ⊆ A ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q)

/-- The integer-distance graph on a point set $A \subseteq \mathbb{R}^2$: vertices are points
of $A$, and two distinct points are adjacent if and only if their Euclidean distance
is a positive integer. -/
noncomputable def intDistGraph (A : Set ℝ²) :
    SimpleGraph ↥A where
  Adj p q := (p : ℝ²) ≠ q ∧
    ∃ n : ℕ, 0 < n ∧ dist (p : ℝ²) (q : ℝ²) = n
  symm := fun _p _q ⟨hne, n, hn, hd⟩ =>
    ⟨hne.symm, n, hn, by rw [_root_.dist_comm]; exact hd⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/--
Erdős Problem 130 [Er97b] (asked by Andrásfai and Erdős):
Let $A \subseteq \mathbb{R}^2$ be an infinite set with no three points collinear and no four
points concyclic. Consider the integer-distance graph $G$ on $A$, where two distinct points
are adjacent if and only if their Euclidean distance is a positive integer.

Can the chromatic number of $G$ be infinite?

Note: The clique number is always finite. The Anning–Erdős theorem [AnEr45]
shows that any infinite set of points in the plane with all pairwise integer
distances must be collinear; since $A$ has no three collinear points, $A$ contains
no infinite complete subgraph.
-/
@[category research open, AMS 5 51]
theorem erdos_130 : answer(sorry) ↔
    ∃ (A : Set ℝ²),
      A.Infinite ∧ ErdosGeneralPosition A ∧
      (intDistGraph A).chromaticNumber = ⊤ := by
  sorry

end Erdos130
