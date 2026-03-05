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
# Erdős Problem 708

*Reference:* [erdosproblems.com/708](https://www.erdosproblems.com/708)

Let $g(n)$ be minimal such that for any $A \subseteq [2,\infty) \cap \mathbb{N}$ with
$|A| = n$ and any set $I$ of $\max(A)$ consecutive integers there exists some
$B \subseteq I$ with $|B| = g(n)$ such that $\prod_{a \in A} a \mid \prod_{b \in B} b$.

Is it true that $g(n) \leq (2+o(1))n$? Or perhaps even $g(n) \leq 2n$?

A problem of Erdős and Surányi [ErSu59], who proved that $g(n) \geq (2-o(1))n$,
and that $g(3) = 4$. Gallai first considered such problems and observed $g(2) = 2$.

[ErSu59] Erdős, P. and Surányi, J., 1959.
-/

open Nat Finset

open scoped BigOperators

namespace Erdos708

/--
Erdős Problem 708 (weak form) [ErSu59]: $g(n) \leq (2+o(1))n$.

For every $\varepsilon > 0$, there exists $N_0$ such that for all nonempty
$A \subseteq \{2, 3, \ldots\}$ with $|A| \geq N_0$ and every interval of $\max(A)$
consecutive natural numbers starting at $k$, there exists a subset $B$ of that interval
with $|B| \leq (2+\varepsilon)|A|$ whose product is divisible by the product of $A$.
-/
@[category research open, AMS 5 11]
theorem erdos_708 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty),
    N₀ ≤ A.card → (∀ a ∈ A, 2 ≤ a) →
    ∀ (k : ℕ),
    ∃ B : Finset ℕ, B ⊆ Finset.Icc k (k + A.max' hA - 1) ∧
      (B.card : ℝ) ≤ (2 + ε) * A.card ∧
      (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  sorry

/--
Erdős Problem 708 (strong form) [ErSu59]: $g(n) \leq 2n$.

For every nonempty finite set $A \subseteq \{2, 3, \ldots\}$ and every interval of
$\max(A)$ consecutive natural numbers starting at $k$, there exists a subset $B$ of that
interval with $|B| \leq 2|A|$ whose product is divisible by the product of $A$.
-/
@[category research open, AMS 5 11]
theorem erdos_708.variants.strong : answer(sorry) ↔
    ∀ (A : Finset ℕ) (hA : A.Nonempty), (∀ a ∈ A, 2 ≤ a) →
    ∀ (k : ℕ),
    ∃ B : Finset ℕ, B ⊆ Finset.Icc k (k + A.max' hA - 1) ∧
      B.card ≤ 2 * A.card ∧
      (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  sorry

end Erdos708
