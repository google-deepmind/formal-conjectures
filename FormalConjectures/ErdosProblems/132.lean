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
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 132

*Reference:* [erdosproblems.com/132](https://www.erdosproblems.com/132)

Let $A \subset \mathbb{R}^2$ be a set of $n$ points. Must there be two
distances which occur at least once but between at most $n$ pairs of points?
Must the number of such distances tend to infinity as $n \to \infty$?

Asked by Erdős and Pach. A "limited-occurrence distance" for $A$ is a value
$d > 0$ such that the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$
and $\mathrm{dist}(x, y) = d$ is between $1$ and $2n = 2|A|$ inclusive.
(Equivalently, the distance is achieved by at most $n$ unordered pairs.)

Hopf and Pannwitz [HoPa34] proved that the largest distance between points
of $A$ can occur at most $n$ unordered pairs (i.e., at most $2n$ ordered
pairs), making it a limited-occurrence distance whenever it is realized.
The question is whether a *second* such distance must also always exist.

Erdős believed that for $n \geq 5$ there must always exist at least two
limited-occurrence distances. Erdős and Fishburn [ErFi95] proved this for
$n = 5$ and $n = 6$. Clemen, Dumitrescu, and Liu [CDL25] proved it for
point sets in convex position.

Erdős offered $100 for "any nontrivial result" [Er97e].

[Er84c] Erdős, P., *Some old and new problems in combinatorial geometry*,
Convexity and graph theory (Jerusalem, 1981), 1984, pp. 129–136.

[ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*,
Combinatorica (1990).

[HoPa34] Hopf, H. and Pannwitz, E., *Aufgabe Nr. 167*,
Jahresbericht der Deutschen Mathematiker-Vereinigung **43** (1934), p. 114.

[ErFi95] Erdős, P. and Fishburn, P., *Multiplicities of interpoint distances in finite
planar sets*, Discrete Applied Mathematics (1995), pp. 141–147.

[Er97b] Erdős, P., *Some of my favourite problems which recently have been solved*,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[Er97e] Erdős, P., *Some of my favourite unsolved problems*,
Mathematics in Japan (1997), pp. 527–537.

[CDL25] Clemen, F., Dumitrescu, A., and Liu, D., *On multiplicities of interpoint
distances*, arXiv:2505.04283 (2025).

See also Problems #223, #756, and #957.
-/

open Classical EuclideanGeometry

namespace Erdos132

/-- For a finite point set $A \subseteq \mathbb{R}^2$ and a real value $d$,
the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$ at
Euclidean distance $d$. -/
noncomputable def pairCount (A : Finset ℝ²) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card

/-- A distance $d$ is a *limited-occurrence distance* for $A$ if it is
achieved by at least one but at most $2|A|$ ordered pairs of distinct
points of $A$ (equivalently, at most $|A|$ unordered pairs). -/
def IsLimitedOccurrence (A : Finset ℝ²) (d : ℝ) : Prop :=
  0 < pairCount A d ∧ pairCount A d ≤ 2 * A.card

/-- The set of all limited-occurrence distances for $A$. -/
noncomputable def limitedOccurrences (A : Finset ℝ²) : Set ℝ :=
  {d : ℝ | IsLimitedOccurrence A d}

/--
Erdős Problem 132, Part 1 [Er84c, ErPa90, ErFi95]:
For any set $A$ of $n \geq 5$ points in the plane $\mathbb{R}^2$, there
must exist at least two distinct limited-occurrence distances.
-/
@[category research open, AMS 5 52]
theorem erdos_132 :
    answer(sorry) ↔
      ∀ A : Finset ℝ², 5 ≤ A.card →
        2 ≤ Set.ncard (limitedOccurrences A) := by
  sorry

/--
Erdős Problem 132, Part 2 [Er84c, ErPa90]:
The number of limited-occurrence distances must tend to infinity with $n$.
For every $k$, there exists $N$ such that any set $A$ of at least $N$ points
in $\mathbb{R}^2$ has at least $k$ limited-occurrence distances.
-/
@[category research open, AMS 5 52]
theorem erdos_132.variants.tend_to_infinity :
    answer(sorry) ↔
      ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℝ², N ≤ A.card →
        k ≤ Set.ncard (limitedOccurrences A) := by
  sorry

/--
Erdős Problem 132, Convex Position Variant [CDL25]:
For any set $A$ of $n \geq 5$ points in convex position in the plane, there
exist at least two limited-occurrence distances. Proved by Clemen, Dumitrescu,
and Liu (2025).
-/
@[category research solved, AMS 5 52]
theorem erdos_132.variants.convex_position :
    ∀ A : Finset ℝ², 5 ≤ A.card → ConvexIndep (↑A : Set ℝ²) →
      2 ≤ Set.ncard (limitedOccurrences A) := by
  sorry

/--
Erdős Problem 132, Small Cases [ErFi95]:
For any set $A$ of exactly $5$ or $6$ points in the plane, there exist at
least two limited-occurrence distances. Proved by Erdős and Fishburn (1995).
-/
@[category research solved, AMS 5 52]
theorem erdos_132.variants.small_cases (A : Finset ℝ²)
    (hA : A.card = 5 ∨ A.card = 6) :
    2 ≤ Set.ncard (limitedOccurrences A) := by
  sorry

end Erdos132
