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
# Erdős Problem 132

*Reference:* [erdosproblems.com/132](https://www.erdosproblems.com/132)

Let $A \subset \mathbb{R}^2$ be a set of $n$ points. Must there be two
distances which occur at least once but between at most $n$ pairs of points?
Must the number of such distances tend to infinity as $n \to \infty$?

Asked by Erdős and Pach. A "limited-occurrence distance" for $A$ is a value
$d > 0$ such that the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$
and $\mathrm{dist}(x, y) = d$ is between $1$ and $n = |A|$ inclusive.

Hopf and Pannowitz [HoPa34] proved that the largest distance between points
of $A$ can occur at most $n$ times, making it a limited-occurrence distance
whenever it is realized. The question is whether a *second* such distance
must also always exist.

Erdős believed that for $n \geq 5$ there must always exist at least two
limited-occurrence distances. Erdős and Fishburn [ErFi95] proved this for
$n = 5$ and $n = 6$. Clemen, Dumitrescu, and Liu [CDL25] proved it for
point sets in convex position.

[Er84c] Erdős, P., *Some old and new problems in combinatorial geometry*, 1984.

[ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*, 1990.

[HoPa34] Hopf, H. and Pannwitz, E., *Aufgabe Nr. 167*, 1934.

[ErFi95] Erdős, P. and Fishburn, P., *Maximum planar sets that determine $k$ distances*, 1995.

[CDL25] Clemen, F., Dumitrescu, A., and Liu, R., *Limited-occurrence distances in convex
position*, 2025.
-/

open Classical

namespace Erdos132

/-- For a finite point set $A \subseteq \mathbb{R}^2$ and a real value $d$,
the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$ at
Euclidean distance $d$. -/
noncomputable def pairCount (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card

/-- A distance $d$ is a *limited-occurrence distance* for $A$ if it is
achieved by at least one but at most $|A|$ ordered pairs of distinct
points of $A$. -/
def IsLimitedOccurrence (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : Prop :=
  0 < pairCount A d ∧ pairCount A d ≤ A.card

/-- The set of all limited-occurrence distances for $A$. -/
noncomputable def limitedOccurrences (A : Finset (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  {d : ℝ | IsLimitedOccurrence A d}

/--
Erdős Problem 132, Part 1 [Er84c, ErPa90, ErFi95]:
For any set $A$ of $n \geq 5$ points in the plane $\mathbb{R}^2$, there
must exist at least two distinct limited-occurrence distances.
-/
@[category research open, AMS 5 52]
theorem erdos_132 :
    answer(sorry) ↔
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
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
      ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
        k ≤ Set.ncard (limitedOccurrences A) := by
  sorry

end Erdos132
