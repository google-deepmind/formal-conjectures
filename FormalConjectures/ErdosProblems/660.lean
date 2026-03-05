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
# Erdős Problem 660

*Reference:* [erdosproblems.com/660](https://www.erdosproblems.com/660)

Let $x_1, \ldots, x_n \in \mathbb{R}^3$ be the vertices of a convex polyhedron. Are there at
least $(1 - o(1))n/2$ many distinct distances between the $x_i$?

For the similar problem in $\mathbb{R}^2$ there are always at least $n/2$ distances,
as proved by Altman [Al63] (see [93]).

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proc. Int. Conf. on Discrete Math. (1997), 527–533.

[Al63] Altman, E., _On a problem of P. Erdős_, Amer. Math. Monthly 70 (1963), 148–157.
-/

namespace Erdos660

/-- Points in $\mathbb{R}^3$ are in convex position if every point is a vertex of the
    convex hull, i.e., no point lies in the convex hull of the remaining points. -/
def InConvexPosition3d (P : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 3)))

/-- The number of distinct pairwise distances determined by a finite point set in
    $\mathbb{R}^3$. -/
noncomputable def distinctDistanceCount3d (P : Finset (EuclideanSpace ℝ (Fin 3))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
**Erdős Problem 660** [Er97e, p.531]:

Let $x_1, \ldots, x_n \in \mathbb{R}^3$ be the vertices of a convex polyhedron. Then the number
of distinct distances determined by these points is at least $(1 - o(1)) \cdot n/2$,
i.e., for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$, the number of
distinct distances is at least $(1 - \varepsilon) \cdot n/2$.
-/
@[category research open, AMS 52]
theorem erdos_660 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 3)),
          P.card = n →
          InConvexPosition3d P →
          (distinctDistanceCount3d P : ℝ) ≥ (1 - ε) * (n : ℝ) / 2 := by
  sorry

end Erdos660
