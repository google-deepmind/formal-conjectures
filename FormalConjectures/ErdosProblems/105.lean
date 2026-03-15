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
# Erdős Problem 105

*Reference:* [erdosproblems.com/105](https://www.erdosproblems.com/105)

Erdős–Purdy conjecture (disproved, $50 prize): given $n$ points in $\mathbb{R}^2$, not all
collinear, and a disjoint set of $n - 3$ points, must there exist a line through at least two
of the first set that avoids the second? Counterexamples were found by Xichuan.

Beck [Be83] and Szemerédi–Trotter [SzTr83] proved the analogous statement holds when
$|B| = cn$ for a constant $c > 0$ (see Problem #211).

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).

[ErPu95] Erdős, P. and Purdy, G., _Two combinatorial problems in the plane_.
Discrete & Computational Geometry (1995), 441–443.

[Be83] Beck, J., _On the lattice property of the plane and some problems of Dirac,
Motzkin and Erdős in combinatorial geometry_. Combinatorica 3 (1983), 281–297.

[SzTr83] Szemerédi, E. and Trotter, W.T., _Extremal problems in discrete geometry_.
Combinatorica 3 (1983), 381–392.
-/

namespace Erdos105

/--
Erdős Problem \#105 (Erdős–Purdy):
Let $A, B \subset \mathbb{R}^2$ be disjoint finite sets with $|A| = n$ and $|B| = n - 3$,
with not all of $A$ contained on a single line. The conjecture asks whether
there must exist a line containing at least two points from $A$ and no points
from $B$.

Note: This conjecture has been disproved. Xichuan found three explicit
counterexamples. It remains open whether the result holds with $n - 4$ (or
more generally with $n - O(1)$ or $(1 - o(1))n$ points in $B$).
The condition $n - 2$ is known to fail via a construction of Hickerson.
-/
@[category research solved, AMS 5 52]
theorem erdos_105 : answer(False) ↔
    ∀ n : ℕ, 3 ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n →
      B.card = n - 3 →
      Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ L.direction = 1 ∧
        2 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
        ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ (B : Set _) → p ∉ L := by
  sorry

end Erdos105
