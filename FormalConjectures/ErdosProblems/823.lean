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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 823

*References:*
- [erdosproblems.com/823](https://www.erdosproblems.com/823)
- [Er59c] Erdős, P., *Remarks on number theory. II. Some problems on the $\sigma$ function*.
  Acta Arith. (1959), 171--177.
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974),
  197-202.
- [Po15b] Pollack, Paul, *Remarks on fibers of the sum-of-divisors function*. Analytic number
  theory, Springer, Cham (2015), 305-320.
-/

@[expose] public section

open Filter Topology
open scoped ArithmeticFunction.sigma Nat

namespace Erdos823

set_option linter.style.formal_proof_palomar false in
/--
Let $\alpha\geq 1$. Is there a sequence of integers $n_k,m_k$ such that $n_k/m_k\to \alpha$ and
$\sigma(n_k)=\sigma(m_k)$ for all $k\geq 1$, where $\sigma$ is the sum of divisors function?

The answer is yes, proved by Pollack [Po15b].

We take $n_k$ and $m_k$ to be positive integers.
-/
@[category research solved, question, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos823.lean#L72"]
theorem erdos_823 : ∀ α : ℝ, 1 ≤ α →
    ∃ n m : ℕ → ℕ, (∀ k, 0 < n k) ∧ (∀ k, 0 < m k) ∧ (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
      Tendsto (fun k ↦ (n k : ℝ) / m k) atTop (𝓝 α) := by
  sorry

/--
For every $\alpha\geq 1$ there are sequences of integers $n_k,m_k$ such that $n_k/m_k\to \alpha$
and $\phi(n_k)=\phi(m_k)$ for all $k\geq 1$. Erdős [Er74b] writes it is 'easy to prove the
analogous result for $\phi(n)$'.
-/
@[category research solved, AMS 11]
theorem erdos_823.variants.totient : ∀ α : ℝ, 1 ≤ α →
    ∃ n m : ℕ → ℕ, (∀ k, 0 < n k) ∧ (∀ k, 0 < m k) ∧ (∀ k, φ (n k) = φ (m k)) ∧
      Tendsto (fun k ↦ (n k : ℝ) / m k) atTop (𝓝 α) := by
  sorry

end Erdos823
