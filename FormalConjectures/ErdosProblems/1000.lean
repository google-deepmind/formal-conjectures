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
# Erdős Problem 1000

*Reference:* [erdosproblems.com/1000](https://www.erdosproblems.com/1000)

Let $A = \{n_1 < n_2 < \cdots\}$ be an infinite sequence of integers, and let $\varphi_A(k)$
count the number of $1 \leq m \leq n_k$ such that the fraction $m/n_k$ does not have
denominator $n_j$ for $j < k$ when written in lowest form; equivalently,
$n_k / \gcd(m, n_k) \neq n_j$ for all $1 \leq j < k$.

Is there a sequence $A$ such that
$$\lim_{N \to \infty} \frac{1}{N} \sum_{k \leq N} \frac{\varphi_A(k)}{n_k} = 0?$$

Erdős believed no such sequence exists. This was solved by Haight [Ha] who
proved that such a sequence does exist (contrary to Erdős' expectations).

[Er64b] Erdős, P., _Some problems in number theory_. 1964.

[Ha] Haight, J. A., _A linear programming problem_. 1979.
-/

open Finset Filter

namespace Erdos1000

/-- For a strictly increasing sequence $a : \mathbb{N} \to \mathbb{N}$ of positive integers,
$\varphi_A(k)$ counts the number of $1 \leq m \leq a(k)$ such that
$a(k) / \gcd(m, a(k)) \neq a(j)$ for all $j < k$. -/
noncomputable def phiA (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (a k)).filter (fun m =>
    ∀ j < k, (a k) / Nat.gcd m (a k) ≠ a j)).card

/--
Erdős Problem 1000 [Er64b]:

There exists a strictly increasing sequence $A = \{n_1 < n_2 < \cdots\}$ of positive
integers such that the Cesàro mean of $\varphi_A(k)/n_k$ tends to $0$:
$$\lim_{N \to \infty} \frac{1}{N} \sum_{k \leq N} \frac{\varphi_A(k)}{n_k} = 0.$$

Proved by Haight [Ha].
-/
@[category research solved, AMS 11]
theorem erdos_1000 : answer(True) ↔
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, (phiA a k : ℝ) / (a k : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end Erdos1000
