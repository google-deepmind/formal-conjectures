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
# Erdős Problem 49

*Reference:* [erdosproblems.com/49](https://www.erdosproblems.com/49)

The maximum size of a subset of $\{1, \ldots, N\}$ on which Euler's totient function is
strictly increasing is $(1 + o(1))\pi(N)$. Proved by Tao.
-/

namespace Erdos49

/--
Let $A = \{a_1 < \cdots < a_t\} \subseteq \{1, \ldots, N\}$ be such that
$\varphi(a_1) < \cdots < \varphi(a_t)$, i.e., the Euler totient function is
strictly increasing on $A$ (in the ordering inherited from $\mathbb{N}$).
The primes are such an example.

The conjecture (proved by Tao) is that $|A| \leq (1 + o(1))\pi(N)$, i.e.,
for every $\varepsilon > 0$, for all sufficiently large $N$, any such $A$
satisfies $|A| \leq (1 + \varepsilon) \cdot \pi(N)$.
-/
@[category research solved, AMS 11]
theorem erdos_49 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) := by
  sorry

end Erdos49
