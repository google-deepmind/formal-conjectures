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
# Erdős Problem 438

*Reference:* [erdosproblems.com/438](https://www.erdosproblems.com/438)

How large can $A \subseteq \{1, \ldots, N\}$ be if $A + A$ contains no square numbers?

Taking all integers $\equiv 1 \pmod{3}$ shows that $|A| \geq N/3$ is possible. This can
be improved to $(11/32)N$ by taking all integers $\equiv 1,5,9,13,14,17,21,25,26,29,30
\pmod{32}$, as observed by Massias.

Khalfalah, Lodha, and Szemerédi [KLS02] proved that the maximal such $A$ satisfies
$|A| \leq (11/32 + o(1))N$, showing that $11/32$ is sharp.

[KLS02] Khalfalah, A., Lodha, S., and Szemerédi, E., _On the density of sumsets not
containing a square_, 2002.
-/

open Finset

namespace Erdos438

/-- No sum of two elements of $A$ is a perfect square. -/
def SumsetAvoidSquares (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬IsSquare (a + b)

/-- Erdős Problem 438 (solved):
For any $\varepsilon > 0$, for all sufficiently large $N$, if $A \subseteq \{1, \ldots, N\}$
and no sum $a + b$ with $a, b \in A$ is a perfect square, then
$|A| \leq (11/32 + \varepsilon) \cdot N$.

Proved by Khalfalah, Lodha, and Szemerédi [KLS02]. -/
@[category research solved, AMS 5 11]
theorem erdos_438 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
    SumsetAvoidSquares A →
    (A.card : ℝ) ≤ (11 / 32 + ε) * (N : ℝ) := by
  sorry

end Erdos438
