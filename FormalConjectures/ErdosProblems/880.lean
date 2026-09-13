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

import FormalConjecturesUtil

/-!
# Erdős Problem 880

*Reference:* [erdosproblems.com/880](https://www.erdosproblems.com/880)
-/

open Filter Set

namespace Erdos880

/-- Sums of `k` or fewer distinct elements of `A`. -/
def boundedDistinctSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  { n | ∃ s : Finset ℕ, ↑s ⊆ A ∧ 1 ≤ s.card ∧ s.card ≤ k ∧ s.sum id = n }

/-- Increasing enumeration of an infinite set of naturals. -/
noncomputable def enum (B : Set ℕ) (n : ℕ) : ℕ := Nat.nth (· ∈ B) n

/--
Let $A\subset\mathbb{N}$ be an additive basis of order $k$. Let $B=\{b_1<b_2<\cdots\}$ be the set of
integers which are the sum of $k$ or fewer distinct $a\in A$. Is it true that $b_{n+1}-b_n=O(1)$?
(Where the implied constant may depend on both $A$ and $k$.)
-/
@[category research open, AMS 11]
theorem erdos_880 :
    answer(sorry) ↔
      ∀ k ≥ 1, ∀ A : Set ℕ, A.IsAddBasisOfOrder k →
        let B := boundedDistinctSums A k
        ∃ C : ℕ, ∀ n : ℕ, enum B (n + 1) - enum B n ≤ C := by
  sorry

end Erdos880
