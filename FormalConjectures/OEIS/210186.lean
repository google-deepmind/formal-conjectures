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
# Least integer $m > 1$ dividing no sum of two distinct primorials up to $P_n$

For $n \ge 1$, $a(n)$ is the least integer $m > 1$ such that $m$ divides none of $P_i + P_j$ with
$0 < i < j \le n$, where $P_k$ is the product of the first $k$ primes.

*References:*
- [A210186](https://oeis.org/A210186)
-/

namespace OeisA210186

/-- Product of the first $k$ primes. -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- Least integer $m > 1$ such that $m$ divides none of $P_i + P_j$ with $0 < i < j \le n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 1 < m ∧
    ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ (m ∣ (primorial i + primorial j)) }

@[category API, AMS 11]
lemma primorial_1 : primorial 1 = 2 := by
  simp [primorial, Nat.nth_prime_zero_eq_two]

@[category API, AMS 11]
lemma primorial_2 : primorial 2 = 6 := by
  simp [primorial, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

@[category API, AMS 11]
lemma primorial_3 : primorial 3 = 30 := by
  simp [primorial, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five]

@[category API, AMS 11]
lemma primorial_4 : primorial 4 = 210 := by
  simp [primorial, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => by omega⟩, fun m hm => hm.1⟩

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => by omega⟩, fun m hm => hm.1⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hi1 : i = 1 := by omega
    have hj2 : j = 2 := by omega
    subst hi1 hj2
    rw [primorial_1, primorial_2]
    decide
  · by_contra! hlt
    have hm2 : m = 2 := by have := hm.1; omega
    subst hm2
    have := hm.2 1 2 (by decide) (by decide) (by decide)
    rw [primorial_1, primorial_2] at this
    exact this (by decide)

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hj_ge : 2 ≤ j := by omega
    interval_cases j
    · have hi1 : i = 1 := by omega
      subst hi1; rw [primorial_1, primorial_2]; decide
    · interval_cases i
      · rw [primorial_1, primorial_3]; decide
      · rw [primorial_2, primorial_3]; decide
  · by_contra! hlt
    have hm_gt : 1 < m := hm.1
    interval_cases m
    · have := hm.2 1 2 (by decide) (by decide) (by decide)
      rw [primorial_1, primorial_2] at this; exact this (by decide)
    · have := hm.2 2 3 (by decide) (by decide) (by decide)
      rw [primorial_2, primorial_3] at this; exact this (by decide)
    · have := hm.2 1 2 (by decide) (by decide) (by decide)
      rw [primorial_1, primorial_2] at this; exact this (by decide)

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨by decide, fun i j hi hij hj => ?_⟩, fun m hm => ?_⟩
  · have hj_ge : 2 ≤ j := by omega
    interval_cases j
    · have hi1 : i = 1 := by omega
      subst hi1; rw [primorial_1, primorial_2]; decide
    · interval_cases i
      · rw [primorial_1, primorial_3]; decide
      · rw [primorial_2, primorial_3]; decide
    · interval_cases i
      · rw [primorial_1, primorial_4]; decide
      · rw [primorial_2, primorial_4]; decide
      · rw [primorial_3, primorial_4]; decide
  · by_contra! hlt
    have hm_gt : 1 < m := hm.1
    interval_cases m
    · have := hm.2 1 2 (by decide) (by decide) (by decide)
      rw [primorial_1, primorial_2] at this; exact this (by decide)
    · have := hm.2 2 3 (by decide) (by decide) (by decide)
      rw [primorial_2, primorial_3] at this; exact this (by decide)
    · have := hm.2 1 2 (by decide) (by decide) (by decide)
      rw [primorial_1, primorial_2] at this; exact this (by decide)
    · have := hm.2 3 4 (by decide) (by decide) (by decide)
      rw [primorial_3, primorial_4] at this; exact this (by decide)
    · have := hm.2 2 3 (by decide) (by decide) (by decide)
      rw [primorial_2, primorial_3] at this; exact this (by decide)

/--
"Conjecture: all the terms are primes and $a(n) < n^2$ for all $n > 1$."
- _Zhi-Wei Sun_, Mar 18 2012
-/
@[category research open, AMS 11]
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → (a n).Prime) ∧ (∀ n : ℕ, 1 < n → a n < n ^ 2) := by
  sorry

end OeisA210186
