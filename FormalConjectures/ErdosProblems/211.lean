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
# Erdős Problem 211

*Reference:* [erdosproblems.com/211](https://www.erdosproblems.com/211)

Let $1 \leq k < n$. Given $n$ points in $\mathbb{R}^2$, at most $n - k$ on any line,
there are $\gg kn$ many lines which contain at least two points.

Proved by Beck [Be83] and Szemerédi–Trotter [SzTr83].

In particular, given any $2n$ points with at most $n$ on a line there
are $\gg n^2$ many lines formed by the points.

[Be83] Beck, J., _On the lattice property of the plane and some problems of Dirac,
Motzkin and Erdős in combinatorial geometry_. Combinatorica 3 (1983), 281-297.

[SzTr83] Szemerédi, E. and Trotter, W.T., _Extremal problems in discrete geometry_.
Combinatorica 3 (1983), 381-392.
-/

open Classical

namespace Erdos211

/-- Points in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- Point $r$ lies on the line through points $p$ and $q$. -/
def LiesOnLine (p q r : Point2) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/-- The line through two points, as a set of points. -/
def lineThrough (p q : Point2) : Set Point2 :=
  {r | LiesOnLine p q r}

/-- The number of points in $S$ on the line through $p$ and $q$. -/
noncomputable def pointsOnLine (S : Finset Point2) (p q : Point2) : ℕ :=
  (S.filter (fun r => LiesOnLine p q r)).card

/-- The number of distinct lines containing at least two points of $S$. -/
noncomputable def lineCount (S : Finset Point2) : ℕ :=
  (((S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2)).image
    (fun pq => lineThrough pq.1 pq.2)).card

/--
Erdős Problem 211 (Proved by Beck [Be83] and Szemerédi–Trotter [SzTr83]):

There exists an absolute constant $C > 0$ such that for any finite set $S$
of points in $\mathbb{R}^2$ with $|S| = n$, if $1 \leq k < n$ and at most $n - k$ points
of $S$ lie on any single line, then the number of distinct lines containing
at least two points of $S$ is at least $C \cdot k \cdot n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_211 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (S : Finset Point2) (k : ℕ),
        1 ≤ k →
        k < S.card →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → pointsOnLine S p q ≤ S.card - k) →
        (lineCount S : ℝ) ≥ C * ↑k * ↑S.card := by
  sorry

end Erdos211
