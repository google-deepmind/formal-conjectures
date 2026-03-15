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
# Erdős Problem 102

*Reference:* [erdosproblems.com/102](https://www.erdosproblems.com/102)

Erdős–Purdy conjecture: if an $n$-point set in $\mathbb{R}^2$ determines at least $cn^2$ lines
each containing more than three points, then some line must contain an unbounded number of
points as $n \to \infty$.

It is not even known whether $h_c(n) \geq 5$ (see Problem 101).

Erdős originally conjectured the stronger bound $h_c(n) \gg_c n^{1/2}$, but this was disproven
by Hunter using point sets in $\{1, \ldots, m\}^d$ projected to $\mathbb{R}^2$, which shows
$h_c(n) \ll n^{1/\log(1/c)}$. It is easy to see that $h_c(n) \ll_c n^{1/2}$.

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44-48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Congressus Numerantium 107 (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.
-/

namespace Erdos102

/--
The number of distinct affine lines in $\mathbb{R}^2$ that contain at least $4$ points from $P$
(i.e., more than $3$ points, as in the problem statement).
-/
noncomputable def fourPlusRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem 102 (Erdős–Purdy):

For fixed $c > 0$, let $h_c(n)$ denote the largest integer $h$ such that: for every
$n$-point set $P$ in $\mathbb{R}^2$ with at least $c \cdot n^2$ lines each containing more than $3$ points
of $P$, some line contains at least $h$ points of $P$. (In other words, $h_c(n)$ is the
minimum, over all such configurations $P$, of the maximum collinearity.)

The conjecture is that $h_c(n) \to \infty$ as $n \to \infty$, i.e., for each fixed $c > 0$ and
each $M \in \mathbb{N}$, there exists $N$ such that for all $n \geq N$, every $n$-point configuration
with at least $c \cdot n^2$ four-rich lines must contain some line with at least $M$ points.
-/
@[category research open, AMS 5 52]
theorem erdos_102 :
  ∀ c : ℝ, c > 0 →
    ∀ M : ℕ,
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
          ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
            Module.finrank ℝ L.direction = 1 ∧
            M ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} := by
  sorry

/--
Erdős Problem 102 (stronger conjecture, disproven):

Erdős originally conjectured that $h_c(n) \gg_c n^{1/2}$, i.e., for each fixed $c > 0$ there
exists a constant $C > 0$ such that for all sufficiently large $n$, every $n$-point configuration
in $\mathbb{R}^2$ with at least $c \cdot n^2$ four-rich lines must contain some line with at least
$C \cdot n^{1/2}$ points. This was disproven by Zach Hunter, who showed that point sets in
$\{1, \ldots, m\}^d$ projected to $\mathbb{R}^2$ yield $h_c(n) \ll n^{1/\log(1/c)}$.
-/
@[category research solved, AMS 5 52]
theorem erdos_102_strong_conjecture_false :
    ¬ (∀ c : ℝ, c > 0 →
      ∃ C : ℝ, C > 0 ∧
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
            P.card = n →
            c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
            ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
              Module.finrank ℝ L.direction = 1 ∧
              C * (n : ℝ) ^ (1/2 : ℝ) ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}) := by
  sorry

end Erdos102
