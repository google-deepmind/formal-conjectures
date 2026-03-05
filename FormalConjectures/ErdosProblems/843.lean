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
# Erdős Problem 843

*Reference:* [erdosproblems.com/843](https://www.erdosproblems.com/843)

A problem of Burr and Erdős [BuEr85]. Proved by Conlon, Fox, and Pham [CFP21],
who showed that the set of $k$-th powers contains a sparse Ramsey $r$-complete
subsequence for every $r, k \geq 2$.
-/

namespace Erdos843

/-- A set $A \subseteq \mathbb{N}$ is Ramsey $r$-complete if for every $r$-colouring of $A$,
every sufficiently large natural number can be written as a sum of
distinct monochromatic elements of $A$. -/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (S : Finset ℕ) (a : Fin r),
      (↑S : Set ℕ) ⊆ A ∧
      (∀ s ∈ S, c s = a) ∧
      S.sum id = n

/--
Erdős Problem 843 [BuEr85][Er92b][Er95]:
The set of perfect squares is Ramsey $2$-complete. That is, for any
$2$-colouring of the squares, every sufficiently large natural number
can be written as a monochromatic sum of distinct squares.

Proved by Conlon, Fox, and Pham [CFP21].
-/
@[category research solved, AMS 5]
theorem erdos_843 :
    answer(True) ↔ IsRamseyComplete {n : ℕ | ∃ m : ℕ, m ≥ 1 ∧ n = m ^ 2} 2 := by
  sorry

end Erdos843
