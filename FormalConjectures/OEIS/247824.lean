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
# Least $m$ such that $m + n$ divides $\mathrm{prime}(m) + \mathrm{prime}(n)$

The sequence $a(n)$ is the least positive integer $m$ such that $m + n$ divides
$\mathrm{prime}(m) + \mathrm{prime}(n)$, where $\mathrm{prime}(k)$ denotes the $k$-th prime number
(with $\mathrm{prime}(1) = 2$).

*References:*
- [A247824](https://oeis.org/A247824)
-/

namespace OeisA247824

open Nat Set

/-- The primary sequence $a(n)$: least positive integer $m$ such that $m + n$ divides
$\mathrm{prime}(m) + \mathrm{prime}(n)$. If no such $m$ exists (or if $n = 0$), it returns $0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  sInf { m : ℕ | 0 < m ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨⟨by omega, ?_⟩, fun m hm => hm.1⟩
  have h : Nat.nth Nat.Prime 0 + Nat.nth Nat.Prime 0 = 2 * Nat.nth Nat.Prime 0 := by ring
  rw [h]
  exact dvd_mul_right 2 _

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨⟨by omega, ?_⟩, fun m hm => ?_⟩
  · norm_num [Nat.nth_prime_four_eq_eleven, Nat.nth_prime_one_eq_three]
  · by_contra! hlt
    have hm1 := hm.1
    interval_cases m
    · revert hm; norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    · revert hm; norm_num [Nat.nth_prime_one_eq_three]
    · revert hm; norm_num [Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three]
    · revert hm; norm_num [Nat.nth_prime_three_eq_seven, Nat.nth_prime_one_eq_three]

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨⟨by omega, ?_⟩, fun m hm => ?_⟩
  · norm_num [Nat.nth_prime_four_eq_eleven, Nat.nth_prime_two_eq_five]
  · by_contra! hlt
    have hm1 := hm.1
    interval_cases m
    · revert hm; norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
    · revert hm; norm_num [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
    · revert hm; norm_num [Nat.nth_prime_two_eq_five]
    · revert hm; norm_num [Nat.nth_prime_three_eq_seven, Nat.nth_prime_two_eq_five]

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨⟨by omega, ?_⟩, fun m hm => ?_⟩
  · norm_num [Nat.nth_prime_four_eq_eleven, Nat.nth_prime_three_eq_seven]
  · by_contra! hlt
    have hm1 := hm.1
    interval_cases m
    · revert hm; norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_three_eq_seven]
    · revert hm; norm_num [Nat.nth_prime_one_eq_three, Nat.nth_prime_three_eq_seven]
    · revert hm; norm_num [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
    · revert hm; norm_num [Nat.nth_prime_three_eq_seven]

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨⟨by omega, ?_⟩, fun m hm => ?_⟩
  · norm_num [Nat.nth_prime_one_eq_three, Nat.nth_prime_four_eq_eleven]
  · by_contra! hlt
    have hm1 := hm.1
    interval_cases m
    · revert hm; norm_num [Nat.nth_prime_zero_eq_two, Nat.nth_prime_four_eq_eleven]

/-- Conjecture: $a(n)$ exists for any $n > 0$. Moreover, $a(n) < n(n-1)$ for all $n > 2$.
The existence of $a(n)$ for $n > 0$ is formalized by requiring that the defining set is nonempty,
which is equivalent to $0 < a(n)$. -/
@[category research open, AMS 11]
theorem conjecture :
    (∀ n : ℕ, 0 < n →
      ({ m : ℕ | 0 < m ∧
        (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }).Nonempty)
    ∧
    (∀ n : ℕ, 2 < n → a n < n * (n - 1)) := by
  sorry

end OeisA247824
