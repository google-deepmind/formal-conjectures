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

*References:*
- [erdosproblems.com/660](https://www.erdosproblems.com/660)
- [Er97e] Erdős, Paul, *Some of my favorite problems and results*, The mathematics of Paul Erdős,
  I (1997), 47–67.
- [Al63] Altman, E., *On a problem of P. Erdős*, Amer. Math. Monthly (1963), 148–157.
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*, Ann. Mat. Pura
  Appl. (4) (1975), 99–108.
-/

open scoped EuclideanGeometry

namespace Erdos660

/--
`P` is the set of vertices of a (full-dimensional) convex polyhedron in $\mathbb{R}^3$: the points
are in convex position and they affinely span $\mathbb{R}^3$ (so the polyhedron is genuinely
three-dimensional).
-/
def IsPolyhedronVertices (P : Finset ℝ³) : Prop :=
  ConvexIndependent ℝ ((↑) : ↥(P : Set ℝ³) → ℝ³) ∧ affineSpan ℝ (P : Set ℝ³) = ⊤

/--
Let $x_1, \ldots, x_n \in \mathbb{R}^3$ be the vertices of a convex polyhedron. Are there at least
$$(1 - o(1)) \frac{n}{2}$$
many distinct distances between the $x_i$?

The $(1 - o(1)) \frac{n}{2}$ lower bound is formalised as: for every $\varepsilon > 0$ there is an
$N$ such that every set of $n \ge N$ vertices of a convex polyhedron determines at least
$(1 - \varepsilon) \frac{n}{2}$ distinct distances.
-/
@[category research open, AMS 51 52]
theorem erdos_660 :
    answer(sorry) ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ³,
        P.card = n → IsPolyhedronVertices P →
        (1 - ε) * ((n : ℝ) / 2) ≤ (EuclideanGeometry.distinctDistances P : ℝ) := by
  sorry

/--
The planar analogue, proved by Altman [Al63]: the $n$ vertices of a convex polygon in the plane
(points in convex position, affinely spanning the plane) determine at least $\lfloor n/2 \rfloor$
distinct distances.
-/
@[category research solved, AMS 51 52]
theorem erdos_660.variants.altman_planar (n : ℕ) (P : Finset ℝ²)
    (hcard : P.card = n) (hconv : ConvexIndependent ℝ ((↑) : ↥(P : Set ℝ²) → ℝ²))
    (haff : affineSpan ℝ (P : Set ℝ²) = ⊤) :
    n / 2 ≤ EuclideanGeometry.distinctDistances P := by
  sorry

end Erdos660
