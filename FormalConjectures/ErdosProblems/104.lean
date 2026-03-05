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
# Erdős Problem 104

*Reference:* [erdosproblems.com/104](https://www.erdosproblems.com/104)

Given $n$ points in $\mathbb{R}^2$, the number of unit circles containing at least three of
the points is $o(n^2)$.
-/

namespace Erdos104

/--
The number of distinct unit circles in $\mathbb{R}^2$ that contain at least three points
from $P$. A unit circle is uniquely determined by its center (since the radius
is fixed at $1$), so two unit circles are distinct iff they have different centers.
-/
noncomputable def threeRichUnitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) |
    3 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ dist p c = 1}}

/--
Given $n$ points in $\mathbb{R}^2$, the number of distinct unit circles containing at least
three points is $o(n^2)$.

Formally: for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ and every
set $P$ of $n$ points in $\mathbb{R}^2$, the number of unit circles (of radius $1$) that each
contain at least $3$ points of $P$ is at most $\varepsilon \cdot n^2$.
-/
@[category research open, AMS 52]
theorem erdos_104 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        (threeRichUnitCircleCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end Erdos104
