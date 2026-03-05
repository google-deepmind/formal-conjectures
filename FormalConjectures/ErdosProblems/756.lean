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
# Erdős Problem 756

*Reference:* [erdosproblems.com/756](https://www.erdosproblems.com/756)

Let $A \subset \mathbb{R}^2$ be a set of $n$ points. Can there be $\gg n$ many
distinct distances each of which occurs for more than $n$ many pairs from $A$?

[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_,
Combinatorica (1990).

[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[Bh24] Bhowmick, A., _On a problem of Erdős and Pach on distances_ (2024).

See also problems #132 and #957.
-/

open Classical

namespace Erdos756

/-- For a finite point set $A \subseteq \mathbb{R}^2$ and a real value $d$,
the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$ at
Euclidean distance $d$. -/
noncomputable def pairCount (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card

/-- The set of distances that occur with multiplicity greater than $|A|$
(counting ordered pairs). -/
noncomputable def highMultiplicityDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  {d : ℝ | A.card < pairCount A d}

/--
Erdős Problem 756 [ErPa90, Er97b] (proved by Bhowmick [Bh24]):
There exists a constant $c > 0$ such that for all sufficiently large $n$,
there is a set $A$ of $n$ points in $\mathbb{R}^2$ with the number of
distinct distances occurring more than $n$ times (as ordered pairs) being
at least $c \cdot n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_756 : answer(True) ↔
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
        c * (n : ℝ) ≤ Set.ncard (highMultiplicityDistances A) := by
  sorry

end Erdos756
