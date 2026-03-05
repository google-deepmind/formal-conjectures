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
# Erdős Problem 537

*Reference:* [erdosproblems.com/537](https://www.erdosproblems.com/537)
-/

open Finset

namespace Erdos537

/--
**Erdős Problem 537** (Disproved by Ruzsa):

Let $\varepsilon > 0$ and $N$ be sufficiently large. If $A \subseteq \{1, \ldots, N\}$ has
$|A| \geq \varepsilon N$, must there exist $a_1, a_2, a_3 \in A$ and distinct primes
$p_1, p_2, p_3$ such that $a_1 p_1 = a_2 p_2 = a_3 p_3$?

A positive answer would imply Problem 536.

Disproved by a construction of Ruzsa: consider the set of all squarefree numbers of the shape
$p_1 \cdots p_r$ where $p_{i+1} > 2p_i$ for $1 \leq i < r$. This set has positive density. If
$A$ is its intersection with $(N/2, N)$ then $|A| \gg N$ for all large $N$, yet no three
elements $a_1, a_2, a_3 \in A$ and distinct primes $p_1, p_2, p_3$ satisfy
$a_1 p_1 = a_2 p_2 = a_3 p_3$.
-/
@[category research solved, AMS 5 11]
theorem erdos_537 : answer(False) ↔
    ∀ (ε : ℝ), 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N → ε * ↑N ≤ ↑A.card →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A,
          ∃ p₁ p₂ p₃ : ℕ,
            Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧
            p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
            a₁ * p₁ = a₂ * p₂ ∧ a₁ * p₁ = a₃ * p₃ := by
  sorry

end Erdos537
