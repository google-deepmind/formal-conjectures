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
# Erdős Problem 322

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)

Let $k \geq 3$ and let $A$ be the set of $k$-th powers. Define $1_A^{(k)}(n)$ as
the number of representations of $n$ as the sum of $k$ many $k$-th powers,
i.e., the number of tuples $(a_1, \ldots, a_k) \in \mathbb{N}^k$ with
$a_1^k + \cdots + a_k^k = n$.

The conjecture asks: for each $k \geq 3$, does there exist some $c > 0$ and
infinitely many $n$ such that $1_A^{(k)}(n) > n^c$?

Connected to Waring's problem. The famous Hypothesis K of Hardy and Littlewood
asserted $1_A^{(k)}(n) \leq n^{o(1)}$, which was disproved by Mahler for $k = 3$,
who showed $1_A^{(3)}(n) \gg n^{1/12}$ for infinitely many $n$. Erdős believed
Hypothesis K fails for all $k \geq 4$, but this remains unknown.
-/

open Finset

open scoped BigOperators

namespace Erdos322

/-- The number of representations of $n$ as a sum of $k$ many $k$-th powers of
natural numbers: $|\{(a_1, \ldots, a_k) \in \mathbb{N}^k : a_1^k + \cdots + a_k^k = n\}|$.
Each component $a_i$ is bounded by $n$ since $a_i^k \leq n$ for $k \geq 1$. -/
noncomputable def kthPowerReps (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin k → Fin (n + 1) =>
    (∑ i, (f i : ℕ) ^ k) = n)).card

/--
**Erdős Problem 322**: For every $k \geq 3$, there exists $c > 0$ such that
the number of representations of $n$ as a sum of $k$ many $k$-th powers
exceeds $n^c$ for infinitely many $n$.
-/
@[category research open, AMS 11]
theorem erdos_322 :
    answer(sorry) ↔
      ∀ k : ℕ, 3 ≤ k →
        ∃ c : ℝ, 0 < c ∧
          ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (kthPowerReps k n : ℝ) > (n : ℝ) ^ c := by
  sorry

end Erdos322
