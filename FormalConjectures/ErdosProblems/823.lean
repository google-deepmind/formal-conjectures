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
# Erdős Problem 823

*Reference:* [erdosproblems.com/823](https://www.erdosproblems.com/823)

Given α ≥ 1, is there a sequence of positive integers n_k, m_k such that n_k / m_k → α and
σ(n_k) = σ(m_k) for all k, where σ is the sum of divisors function? The answer is yes, proved by
Pollack.

[Er59c] Erdős, P., 1959.

[Er74b] Erdős, P., 1974.

[Po15b] Pollack, P., 2015.
-/

open Finset Filter

open scoped BigOperators Topology

namespace Erdos823

/-- The sum of divisors function $\sigma(n) = \sum_{d \mid n} d$. -/
noncomputable def Nat.sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/--
Erdős Problem 823 [Er59c] [Er74b]:

Let $\alpha \geq 1$. Is there a sequence of positive integers $n_k, m_k$ such that
$n_k / m_k \to \alpha$ and $\sigma(n_k) = \sigma(m_k)$ for all $k \geq 1$, where $\sigma$ is the
sum of divisors function?

The answer is yes, proved by Pollack [Po15b].
-/
@[category research solved, AMS 11]
theorem erdos_823 : answer(True) ↔
    ∀ (α : ℝ), α ≥ 1 →
      ∃ (n m : ℕ → ℕ), (∀ k, 0 < n k) ∧ (∀ k, 0 < m k) ∧
      (∀ k, Nat.sumDivisors (n k) = Nat.sumDivisors (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  sorry

end Erdos823
