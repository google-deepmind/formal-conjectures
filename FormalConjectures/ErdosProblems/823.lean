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

Erdős [Er74b] observed that it is easy to prove the analogous result for φ(n) (Euler's totient
function).

[Er59c] Erdős, P., _Remarks on number theory II. Some problems on the σ function_.
Acta Arith. 5 (1959), 171-177.

[Er74b] Erdős, P., _On abundant-like numbers_. Canad. Math. Bull. 17 (1974), 599-602.

[Po15b] Pollack, P., _Remarks on fibers of the sum-of-divisors function_. (2015), 305-320.
-/

open Finset Filter

open scoped ArithmeticFunction.sigma BigOperators Topology

namespace Erdos823

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
      (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  sorry

/--
Variant of Erdős Problem 823 for Euler's totient function φ(n):

Erdős [Er74b] observed that it is easy to prove the analogous result for φ(n). That is,
for every α ≥ 1, there exist sequences of positive integers n_k, m_k such that
n_k / m_k → α and φ(n_k) = φ(m_k) for all k.
-/
@[category research solved, AMS 11]
theorem erdos_823_totient :
    ∀ (α : ℝ), α ≥ 1 →
      ∃ (n m : ℕ → ℕ), (∀ k, 0 < n k) ∧ (∀ k, 0 < m k) ∧
      (∀ k, Nat.totient (n k) = Nat.totient (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  sorry

end Erdos823
