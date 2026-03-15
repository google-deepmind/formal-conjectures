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
# Erdős Problem 880

*Reference:* [erdosproblems.com/880](https://www.erdosproblems.com/880)

Let $A \subset \mathbb{N}$ be an additive basis of order $k$. Let
$B = \{b_1 < b_2 < \cdots\}$ be the set of integers which are the sum of $k$ or fewer
distinct $a \in A$. Is it true that $b_{n+1} - b_n = O(1)$?

A problem of Burr and Erdős [Er98]. Hegyvári, Hennecart, and Plagne [HHP07] showed the
answer is yes for $k = 2$ (in fact with $b_{n+1} - b_n \leq 2$ for sufficiently large $n$)
but no for $k \geq 3$.

[Er98] Erdős, P., _Some of my new and almost new problems and results in
combinatorial number theory_. Number theory (Eger, 1996) (1998), 169–180.

[HHP07] Hegyvári, N., Hennecart, F., Plagne, A., _Answer to a question by Burr and Erdős on
restricted addition, and related results_. Combinatorics, Probability and Computing (2007),
747–756.
-/

open Finset BigOperators

namespace Erdos880

/-- A set $A \subseteq \mathbb{N}$ is an additive basis of order $k$ if every sufficiently large
natural number can be written as a sum of at most $k$ elements from $A$
(with repetition allowed). -/
def IsAdditiveBasis880 (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (l : List ℕ), l.length ≤ k ∧ (∀ x ∈ l, x ∈ A) ∧ l.sum = n

/-- The set of natural numbers expressible as the sum of at most $k$ distinct
elements of $A$. -/
def DistinctSumSet880 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (S : Finset ℕ), (∀ x ∈ S, x ∈ A) ∧ S.card ≤ k ∧ S.sum id = n}

/--
Erdős Problem 880:

Let $A \subset \mathbb{N}$ be an additive basis of order $k$, and let $B$ be the set of
integers expressible as sums of $k$ or fewer distinct elements of $A$. Is it true that
$b_{n+1} - b_n = O(1)$?

The answer is **no** in general. Hegyvári, Hennecart, and Plagne [HHP07] showed that
the answer is yes for $k = 2$ but no for $k \geq 3$.
-/
@[category research solved, AMS 11]
theorem erdos_880 : answer(False) ↔
    ∀ (k : ℕ) (A : Set ℕ), IsAdditiveBasis880 A k →
    ∃ C N₀ : ℕ, ∀ b ∈ DistinctSumSet880 A k, b ≥ N₀ →
    ∃ b' ∈ DistinctSumSet880 A k, b < b' ∧ b' ≤ b + C := by
  sorry

/--
Erdős Problem 880, positive result for $k = 2$ (Hegyvári–Hennecart–Plagne [HHP07]):

If $A$ is an additive basis of order $2$, then the distinct sum set $B$ of $A$ (sums of
at most $2$ distinct elements) has gaps bounded by $2$ for all sufficiently large
elements: for large enough $b \in B$, the next element of $B$ is at most $b + 2$.
-/
@[category research solved, AMS 11]
theorem erdos_880.variants.bounded_gaps_k_eq_2 (A : Set ℕ) (hA : IsAdditiveBasis880 A 2) :
    ∃ N₀ : ℕ, ∀ b ∈ DistinctSumSet880 A 2, b ≥ N₀ →
    ∃ b' ∈ DistinctSumSet880 A 2, b < b' ∧ b' ≤ b + 2 := by
  sorry

/--
Erdős Problem 880, counterexample for $k \geq 3$ (Hegyvári–Hennecart–Plagne [HHP07]):

For every $k \geq 3$, there exists an additive basis $A$ of order $k$ whose distinct sum
set has unbounded gaps.
-/
@[category research solved, AMS 11]
theorem erdos_880.variants.unbounded_gaps_k_ge_3 :
    ∀ k : ℕ, k ≥ 3 →
    ∃ A : Set ℕ, IsAdditiveBasis880 A k ∧
    ∀ C : ℕ, ∃ b ∈ DistinctSumSet880 A k,
      ∀ b' ∈ DistinctSumSet880 A k, b < b' → b + C < b' := by
  sorry

end Erdos880
