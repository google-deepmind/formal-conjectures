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

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

/-!
# Untouchable numbers

A natural number $m$ is *untouchable* (or *nonaliquot*, OEIS A005114) when no natural number $n$
has proper-divisor sum $s(n) = \sigma(n) - n$ equal to $m$.

*References:*
- [Wikipedia, Untouchable number](https://en.wikipedia.org/wiki/Untouchable_number)
- [OEIS A005114](https://oeis.org/A005114)
-/

open scoped ArithmeticFunction.sigma

namespace Nat

/-- A natural number $m$ is untouchable when no $n : \mathbb{N}$ satisfies
$\sum_{d \in \mathrm{properDivisors}(n)} d = m$. Both $n = 0$ and $n = 1$ have proper-divisor sum
$0$, so $0$ is automatically excluded from `IsUntouchable`. -/
def IsUntouchable (m : ℕ) : Prop :=
  ¬ ∃ n : ℕ, ∑ d ∈ n.properDivisors, d = m

/-- For every $n : \mathbb{N}$ (including $n = 0$), $\sigma_1(n) - n$ equals the sum of proper
divisors of $n$. -/
theorem sigma_one_sub_self (n : ℕ) : σ 1 n - n = ∑ d ∈ n.properDivisors, d := by
  rw [ArithmeticFunction.sigma_one_apply, sum_divisors_eq_sum_properDivisors_add_self,
    Nat.add_sub_cancel]

/-- Equivalence between `Nat.IsUntouchable` and lying outside the range of
$n \mapsto \sigma_1(n) - n$. -/
theorem isUntouchable_iff_sigma {m : ℕ} :
    m.IsUntouchable ↔ m ∉ { (σ 1 n - n : ℕ) | n } := by
  simp [IsUntouchable, sigma_one_sub_self]

@[simp]
theorem not_isUntouchable_zero : ¬ IsUntouchable 0 :=
  fun h => h ⟨1, by decide⟩

@[simp]
theorem not_isUntouchable_one : ¬ IsUntouchable 1 :=
  fun h => h ⟨2, by decide⟩

theorem IsUntouchable.two_le {m : ℕ} (hm : m.IsUntouchable) : 2 ≤ m := by
  rcases m with _ | _ | m
  · exact (not_isUntouchable_zero hm).elim
  · exact (not_isUntouchable_one hm).elim
  · omega

end Nat
