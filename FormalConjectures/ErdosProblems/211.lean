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

Erdős conjectured that the bound might be sharpened to $\geq (1 + o(1)) kn / 6$ lines,
though he acknowledged this "perhaps is too optimistic."

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 105.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica 1 (1981), 25–42.

[Er83c] Erdős, P., _Old and new problems in combinatorial analysis and graph theory_, 1983.

[Er84] Erdős, P., _Some old and new problems on combinatorial geometry_, 1984.

[Be83] Beck, J., _On the lattice property of the plane and some problems of Dirac,
Motzkin and Erdős in combinatorial geometry_. Combinatorica 3 (1983), 281-297.

[SzTr83] Szemerédi, E. and Trotter, W.T., _Extremal problems in discrete geometry_.
Combinatorica 3 (1983), 381-392.

[BGS74] Burr, S. A., Grünbaum, B., and Sloane, N. J. A., _The orchard problem_.
Geometriae Dedicata (1974), 397–424.

[FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of
triangles_. Proc. Amer. Math. Soc. **92** (1984), 561–566.
-/

open Classical

namespace Erdos211

/-- The number of points in $S$ on the line through $p$ and $q$,
where the line is defined as the affine span of $\{p, q\}$. -/
noncomputable def pointsOnLine (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (S.filter (fun r => r ∈ affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))))).card

/-- The number of distinct lines containing at least two points of $S$,
where lines are represented as affine subspaces via `affineSpan`. -/
noncomputable def lineCount (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2)).image
    (fun pq => affineSpan ℝ ({pq.1, pq.2} : Set (EuclideanSpace ℝ (Fin 2))))).card

/--
Erdős Problem 211 (Proved by Beck [Be83] and Szemerédi–Trotter [SzTr83])
[Er75f] [Er81] [Er83c] [Er84]:

There exists an absolute constant $C > 0$ such that for any finite set $S$
of points in $\mathbb{R}^2$ with $|S| = n$, if $1 \leq k < n$ and at most $n - k$ points
of $S$ lie on any single line, then the number of distinct lines containing
at least two points of $S$ is at least $C \cdot k \cdot n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_211 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ),
        1 ≤ k →
        k < S.card →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → pointsOnLine S p q ≤ S.card - k) →
        (lineCount S : ℝ) ≥ C * ↑k * ↑S.card := by
  sorry

/--
Erdős Problem 211, special case $k = n$: given $2n$ points with at most $n$ on
any line, there are $\gg n^2$ distinct lines. This corresponds to setting $k = n$
in a set of $2n$ points in the main theorem.
-/
@[category research solved, AMS 5 52]
theorem erdos_211_special :
    ∃ C : ℝ, C > 0 ∧
      ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ),
        S.card = 2 * n →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → pointsOnLine S p q ≤ n) →
        (lineCount S : ℝ) ≥ C * ↑n ^ 2 := by
  sorry

/--
Erdős Problem 211, sharpened conjecture: the constant in the lower bound
can be taken as $(1/6 - \varepsilon)$ for sufficiently large point sets.
Erdős himself described this as possibly "too optimistic."
-/
@[category research open, AMS 5 52]
theorem erdos_211_sharp :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ),
        S.card ≥ N₀ → 1 ≤ k → k < S.card →
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → pointsOnLine S p q ≤ S.card - k) →
        (lineCount S : ℝ) ≥ (1/6 - ε) * ↑k * ↑S.card := by
  sorry

end Erdos211
