/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 469

*Reference:* [erdosproblems.com/469](https://www.erdosproblems.com/469)
-/

namespace Erdos469

/-- The proposition that `n` is a sum of distinct proper divisors. -/
def Nat.IsSumDivisors (n : ℕ) : Prop :=
  ∃ S ⊆ n.properDivisors, ∑ d ∈ S, d = n

open Erdos469

/--
Let $A$ be the set of all $n$ such that $n = d_1 + ⋯ + d_k$ with $d_i$ distinct
proper divisors of $n$, but this is not true for any $m ∣ n$ with $m < n$. Does:
$$
  \sum_{n ∈ A} \frac 1 n
$$
converge?
-/
@[category research open, AMS 11]
theorem erdos_469 :
    letI A := {n : ℕ | 0 < n ∧ n.IsSumDivisors ∧ ∀ m < n, m ∣ n → ¬ m.IsSumDivisors}
    (Summable fun n : A ↦ 1 / (n : ℝ)) ↔ answer(sorry) := by
  sorry

end Erdos469
