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
# Erdős Problem 101

*Reference:* [erdosproblems.com/101](https://www.erdosproblems.com/101)

Given $n$ points in $\mathbb{R}^2$ with no five collinear, the number of lines containing at
least four of the points is $o(n^2)$.
-/

namespace Erdos101

/--
A finite point set in $\mathbb{R}^2$ has no five collinear points if every five-element subset
is not collinear (i.e., no line contains five or more of the points).
-/
def NoFiveCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 5 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of $4$-rich lines: the number of distinct affine lines in $\mathbb{R}^2$ that
contain at least four points from $P$.

An affine line is a $1$-dimensional affine subspace (`Module.finrank` of its
direction submodule equals $1$).
-/
noncomputable def fourRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #101: Given $n$ points in $\mathbb{R}^2$, no five of which are collinear,
the number of lines containing at least four of the points is $o(n^2)$.

Formally: for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ and every
set $P$ of $n$ points in $\mathbb{R}^2$ with no five collinear, the count of $4$-rich lines
is at most $\varepsilon \cdot n^2$.
-/
@[category research open, AMS 5 52]
theorem erdos_101 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          NoFiveCollinear P →
          (fourRichLineCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos101
