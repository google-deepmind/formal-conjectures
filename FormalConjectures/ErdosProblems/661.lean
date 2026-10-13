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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 661

*References:*
- [erdosproblems.com/661](https://www.erdosproblems.com/661)
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica (1990), 261--269.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44-48.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [Er46] Erdős, Paul, *On sets of distances of $n$ points*. Amer. Math. Monthly 53 (1946),
  248--250.
-/

@[expose] public section

open Filter Finset EuclideanGeometry

namespace Erdos661

variable {X : Type*} [MetricSpace X]

/-- The set of distances $d(x, y)$ with $x \in A$ and $y \in B$. -/
noncomputable def crossDistanceSet (A B : Finset X) : Finset ℝ :=
  (A ×ˢ B).image fun p : X × X => dist p.1 p.2

variable (X) in
/-- The minimal number of distinct distances $d(x_i, y_j)$ over all choices of $2n$ distinct
points $x_1, \ldots, x_n, y_1, \ldots, y_n$ in `X`.

The $x_i$ form a set `A` of $n$ points, the $y_j$ form a set `B` of $n$ points, and `A` and `B`
are disjoint, so all $2n$ points are distinct. -/
noncomputable def minimalCrossDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧
    #(crossDistanceSet A B) = m}

/--
Are there, for all large $n$, some points $x_1,\ldots,x_n,y_1,\ldots,y_n\in \mathbb{R}^2$ such that
the number of distinct distances $d(x_i,y_j)$ is
$$o\left(\frac{n}{\sqrt{\log n}}\right)?$$

We require all $2n$ points to be distinct; without any distinctness one could take all points
equal and get a single distance. Writing $F(n)$ for the minimal number of such distances
(`minimalCrossDistances ℝ² n`), the question asks whether $F(n) = o(n / \sqrt{\log n})$. This is
equivalent to the existence, for all large $n$, of configurations whose count is at most $g(n)$
for some fixed $g(n) = o(n / \sqrt{\log n})$, since the infimum is attained.

The source adds that one can also ask this for points in $\mathbb{R}^3$. Taken literally, the
question is easy there, since a cubic grid of $2n$ points determines only $O(n^{2/3})$ distinct
distances, so we do not state it.
-/
@[category research open, AMS 52]
theorem erdos_661 : answer(sorry) ↔
    (fun n => (minimalCrossDistances ℝ² n : ℝ)) =o[atTop]
      (fun (n : ℕ) => (n : ℝ) / (n : ℝ).log.sqrt) := by
  sorry

/--
Take $2n$ points of the smallest square grid with at least $2n$ points; by [Er46] they determine
$O(n / \sqrt{\log n})$ distinct distances. Splitting them into two halves of $n$ points shows
that $F(n) = O(n / \sqrt{\log n})$. So the question is whether this trivial bound can be
improved by more than a constant factor.
-/
@[category research solved, AMS 52]
theorem erdos_661.variants.grid_upper_bound :
    (fun n => (minimalCrossDistances ℝ² n : ℝ)) =O[atTop]
      (fun (n : ℕ) => (n : ℝ) / (n : ℝ).log.sqrt) := by
  sorry

/--
Every split of a set of $2n$ points into two halves of $n$ points gives a configuration for
$F(n)$, and the distances between the halves are among the distances of the whole set. Hence
$F(n) \leq f(2n)$, where $f(2n)$ is the minimal number of distinct distances determined by $2n$
points in $\mathbb{R}^2$.
-/
@[category textbook, AMS 52]
theorem erdos_661.variants.le_minimalDistinctDistances (n : ℕ) :
    minimalCrossDistances ℝ² n ≤ minimalDistinctDistances ℝ² (2 * n) := by
  sorry

/--
Let $F(2n)$ be the minimal number of distinct distances $d(x_i, y_j)$ for $2n$ distinct points
$x_1,\ldots,x_n,y_1,\ldots,y_n\in \mathbb{R}^2$, and $f(2n)$ the minimal number of distinct
distances determined by any $2n$ points in $\mathbb{R}^2$. Is $F = o(f)$?

Here $F(2n)$ of erdosproblems.com is `minimalCrossDistances ℝ² n` (indexed by $n$ points on each
side) and $f(2n)$ is `minimalDistinctDistances ℝ² (2 * n)`. See also Erdős Problem 89.
-/
@[category research open, AMS 52]
theorem erdos_661.variants.little_o_distinct_distances : answer(sorry) ↔
    (fun n => (minimalCrossDistances ℝ² n : ℝ)) =o[atTop]
      (fun n => (minimalDistinctDistances ℝ² (2 * n) : ℝ)) := by
  sorry

/--
In $\mathbb{R}^4$ Lenz observed (as stated on erdosproblems.com/661) that for every $n$ there are
$2n$ distinct points $x_1,\ldots,x_n,y_1,\ldots,y_n\in \mathbb{R}^4$ with $d(x_i,y_j)=1$ for all
$i,j$: take the $x_i$ on the circle of radius $1/\sqrt{2}$ about the origin in the plane of the
first two coordinates, and the $y_j$ on the circle of radius $1/\sqrt{2}$ about the origin in the
plane of the last two coordinates.
-/
@[category research solved, AMS 52]
theorem erdos_661.variants.lenz (n : ℕ) :
    ∃ A B : Finset (EuclideanSpace ℝ (Fin 4)), #A = n ∧ #B = n ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, dist x y = 1 := by
  sorry

end Erdos661
