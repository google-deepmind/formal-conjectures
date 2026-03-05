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

Let $A \subseteq \mathbb{R}^2$ be an infinite set with no three collinear and no four concyclic
points. Can the integer-distance graph on $A$ (adjacent iff at integer distance) have infinite
chromatic number?

[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[AnEr45] Anning, N.H. and Erdős, P., _Integral distances_, Bull. Amer. Math. Soc. (1945),
598-600.
-/

open SimpleGraph

namespace Erdos130

/-- A set of four points in $\mathbb{R}^2$ is concyclic if they all lie on a common circle
(i.e., there exist a center $O \in \mathbb{R}^2$ and radius $r > 0$ such that each of the
four points is at distance $r$ from $O$). -/
def Concyclic (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ),
    0 < radius ∧
    dist a center = radius ∧
    dist b center = radius ∧
    dist c center = radius ∧
    dist d center = radius

/-- A point set $A \subseteq \mathbb{R}^2$ is in Erdős general position if no three distinct
points of $A$ are collinear, and no four distinct points of $A$ are concyclic. -/
def ErdosGeneralPosition (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A →
    p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  (∀ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A → s ∈ A →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬Concyclic p q r s)

/-- The integer-distance graph on a point set $A \subseteq \mathbb{R}^2$: vertices are points
of $A$, and two distinct points are adjacent if and only if their Euclidean distance
is a positive integer. -/
noncomputable def intDistGraph (A : Set (EuclideanSpace ℝ (Fin 2))) :
    SimpleGraph ↥A where
  Adj p q := (p : EuclideanSpace ℝ (Fin 2)) ≠ q ∧
    ∃ n : ℕ, 0 < n ∧ dist (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 2)) = n
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
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))),
      A.Infinite ∧ ErdosGeneralPosition A ∧
      (intDistGraph A).chromaticNumber = ⊤ := by
  sorry

end Erdos130
