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

end Erdos102
