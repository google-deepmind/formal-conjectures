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

[Bh24] Bhowmick, K., _A problem of Erdős about rich distances_. arXiv:2407.01174 (2024).

[CDL25] Clemen, F., Dumitrescu, A., and Liu, D., _On multiplicities of interpoint
distances_. arXiv:2505.04283 (2025).

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
Erdős Problem 756 [ErPa90] (proved by Bhowmick [Bh24]):
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

/--
Stronger variant of Erdős Problem 756 (Erdős–Pach [ErPa90]): for sufficiently
large $n$, there exists a set $A$ of $n$ points in $\mathbb{R}^2$ such that every
realized distance except the largest occurs with multiplicity greater than $|A|$
(as ordered pairs). Hopf and Pannwitz (1934) showed the largest distance occurs
at most $n$ times, so it must be excluded.
-/
@[category research open, AMS 5 52]
theorem erdos_756_all_except_largest :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
        ∀ d : ℝ, 0 < pairCount A d →
          (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y > d) →
          A.card < pairCount A d := by
  sorry

end Erdos756
