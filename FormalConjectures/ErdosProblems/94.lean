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
# Erdős Problem 94

*Reference:* [erdosproblems.com/94](https://www.erdosproblems.com/94)

For $n$ points in convex position with distance multiplicities $f(u_i)$, the sum
$\sum_i f(u_i)^2$ is $O(n^3)$. Proved by Lefmann and Thiele [LeTh95] under the weaker
assumption that no three points are collinear.

Erdős and Fishburn conjectured that $\sum f(u_i)^2$ is maximized by the regular
$n$-gon (for sufficiently large $n$).

See also Problem 95, which is the general (non-convex) version with the weaker bound
$O(n^{3+\varepsilon})$.

Erdős offered £25 for this problem [Er92e].

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44-48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Congressus Numerantium 107 (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)

[LeTh95] Lefmann, H. and Thiele, T., _Point sets with distinct distances_.
Combinatorica 15 (1995), 379–408.
-/

open EuclideanGeometry

namespace Erdos94

/-- The number of ordered pairs `(a, b)` in `A` with `a ≠ b` and `dist a b = d`. -/
noncomputable def distCount (A : Finset ℝ²) (d : ℝ) : ℕ :=
  (A.offDiag.filter fun p => dist p.1 p.2 = d).card

/-- The sum $\sum_i g(u_i)^2$ over distinct distances $u_i$, where $g(u_i)$ counts
ordered pairs at distance $u_i$. This equals $4 \sum_i f(u_i)^2$ where $f$ counts
unordered pairs, so an $O(n^3)$ bound on this sum is equivalent. -/
noncomputable def sumSqDistCount (A : Finset ℝ²) : ℕ :=
  (A.offDiag.image fun p => dist p.1 p.2).sum fun d => distCount A d ^ 2

/-- The vertices of a regular `n`-gon inscribed in the unit circle. -/
noncomputable def regularNGonVertices (n : ℕ) : Finset ℝ² :=
  Finset.image (fun k : Fin n =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![Real.cos (2 * Real.pi * ↑k / ↑n), Real.sin (2 * Real.pi * ↑k / ↑n)])
    Finset.univ

/--
Suppose $n$ points in $\mathbb{R}^2$ are in convex position (they form the vertices of
a convex polygon). Let $\{u_1, \ldots, u_t\}$ be the set of distinct pairwise
distances, and let $f(u_i)$ denote the number of pairs at distance $u_i$. Then
$$\sum_i f(u_i)^2 \ll n^3.$$

This was proved by Lefmann and Thiele [LeTh95] under the weaker
assumption that no three points are collinear (see `erdos_94_no_three_collinear`).
-/
@[category research solved, AMS 5 52]
theorem erdos_94 :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset ℝ²,
      ConvexIndep (↑A : Set ℝ²) →
      (sumSqDistCount A : ℝ) ≤ C * (A.card : ℝ) ^ 3 := by
  sorry

/--
Stronger version of Erdős Problem 94: the $O(n^3)$ bound on $\sum_i f(u_i)^2$ holds
under the weaker hypothesis that no three points are collinear. This is the result
actually proved by Lefmann and Thiele [LeTh95].
-/
@[category research solved, AMS 5 52]
theorem erdos_94_no_three_collinear :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset ℝ²,
      NonTrilinear (↑A : Set ℝ²) →
      (sumSqDistCount A : ℝ) ≤ C * (A.card : ℝ) ^ 3 := by
  sorry

/--
Erdős–Fishburn conjecture: for sufficiently large $n$, the sum $\sum_i f(u_i)^2$ over
distance multiplicities of $n$ points in convex position is maximized by the vertices
of a regular $n$-gon.
-/
@[category research open, AMS 5 52]
theorem erdos_94_fishburn :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℝ², A.card = n →
      ConvexIndep (↑A : Set ℝ²) →
      sumSqDistCount A ≤ sumSqDistCount (regularNGonVertices n) := by
  sorry

end Erdos94
