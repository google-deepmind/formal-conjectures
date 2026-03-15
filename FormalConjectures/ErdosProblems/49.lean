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
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Erdős Problem 49

*Reference:* [erdosproblems.com/49](https://www.erdosproblems.com/49)

The maximum size of a subset of $\{1, \ldots, N\}$ on which Euler's totient function is
strictly increasing is $(1 + o(1))\pi(N)$. Proved by Tao [Ta23b].
See also [Er95], [Er95c].

OEIS: [A365339](https://oeis.org/A365339), [A365474](https://oeis.org/A365474).

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium **107** (1995).

[Er95c] Erdős, P., _Some problems in number theory_. Octogon Math. Mag. (1995), 3–5.

[Ta23b] Tao, T., _Monotone non-decreasing sequences of the Euler totient function_.
arXiv:2309.02325 (2023).
-/

namespace Erdos49

open scoped ArithmeticFunction.sigma

/--
Let $A = \{a_1 < \cdots < a_t\} \subseteq \{1, \ldots, N\}$ be such that
$\varphi(a_1) < \cdots < \varphi(a_t)$, i.e., the Euler totient function is
strictly increasing on $A$ (in the ordering inherited from $\mathbb{N}$).
The primes are such an example.

The conjecture (proved by Tao [Ta23b]) is that $|A| \leq (1 + o(1))\pi(N)$, i.e.,
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

/--
Weaker form of Erdős Problem 49: the maximum size of a subset $A \subseteq \{1, \ldots, N\}$
on which Euler's totient function is strictly increasing satisfies $|A| = o(N)$.
This is implied by the main result `erdos_49`.
-/
@[category research solved, AMS 11]
theorem erdos_49_weaker :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
      (A.card : ℝ) ≤ ε * (N : ℝ) := by
  sorry

/--
Variant of Erdős Problem 49 for the sum-of-divisors function $\sigma(n)$:
what is the maximum size of a subset $A \subseteq \{1, \ldots, N\}$ on which
$\sigma$ is strictly increasing? Is it $(1 + o(1))\pi(N)$?
-/
@[category research open, AMS 11]
theorem erdos_49_sigma :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → σ 1 a < σ 1 b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) := by
  sorry

/--
Variant of Erdős Problem 49 with non-strict monotonicity [Er95c]:
what is the maximum size of a subset $A = \{a_1 < \cdots < a_t\} \subseteq \{1, \ldots, N\}$
such that $\varphi(a_1) \leq \cdots \leq \varphi(a_t)$? Is it $(1 + o(1))\pi(N)$?
-/
@[category research open, AMS 11]
theorem erdos_49_nonstrict :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a ≤ Nat.totient b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) := by
  sorry

end Erdos49
