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
# Number of primes in $n$-th row of triangle $k^2 - k + p_n$

$a(n)$ is the number of primes in the $n$-th row of the triangle $T(n, k) = k^2 - k + p_n$
for $1 \le k \le n$, where $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).

*References:*
- [A117531](https://oeis.org/A117531)-/

namespace OeisA117531

/-- Number of primes in the $n$-th row of $T(n, k) = k^2 - k + p_n$ for $1 \le k \le n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card ((Finset.Icc 1 n).filter fun k => (k ^ 2 - k + pn).Prime)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  have h_zero : Nat.nth Nat.Prime (1 - 1) = 2 := Nat.nth_prime_zero_eq_two
  dsimp only
  rw [h_zero]
  have h1 : Finset.Icc 1 1 = {1} := by decide
  rw [h1]
  have : (Finset.filter (fun k : ℕ => (k ^ 2 - k + 2).Prime) {1}) = {1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h; exact h.1
    · rintro rfl; exact ⟨rfl, by norm_num⟩
  rw [this, Finset.card_singleton]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  unfold a
  have h_one : Nat.nth Nat.Prime (2 - 1) = 3 := Nat.nth_prime_one_eq_three
  dsimp only
  rw [h_one]
  have h2 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h2]
  have : (Finset.filter (fun k : ℕ => (k ^ 2 - k + 3).Prime) {1, 2}) = {1, 2} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; exact h.1
    · rintro (rfl | rfl)
      · refine ⟨Or.inl rfl, by norm_num⟩
      · refine ⟨Or.inr rfl, by norm_num⟩
  rw [this, Finset.card_pair (by decide)]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  unfold a
  have h_two : Nat.nth Nat.Prime (3 - 1) = 5 := Nat.nth_prime_two_eq_five
  dsimp only
  rw [h_two]
  have h3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [h3]
  have : (Finset.filter (fun k : ℕ => (k ^ 2 - k + 5).Prime) {1, 2, 3}) = {1, 2, 3} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; exact h.1
    · rintro (rfl | rfl | rfl)
      · refine ⟨Or.inl rfl, by norm_num⟩
      · refine ⟨Or.inr (Or.inl rfl), by norm_num⟩
      · refine ⟨Or.inr (Or.inr rfl), by norm_num⟩
  rw [this]
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  unfold a
  have h_three : Nat.nth Nat.Prime (4 - 1) = 7 := Nat.nth_prime_three_eq_seven
  dsimp only
  rw [h_three]
  have h4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  rw [h4]
  have : (Finset.filter (fun k : ℕ => (k ^ 2 - k + 7).Prime) {1, 2, 3, 4}) = {1, 3, 4} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | rfl | rfl), hp⟩
      · exact Or.inl rfl
      · exfalso; revert hp; norm_num
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · refine ⟨Or.inl rfl, by norm_num⟩
      · refine ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num⟩
      · refine ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num⟩
  rw [this]
  decide

/--
Conjecture: $a(n) < n$ for $n > 13$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (h : n > 13) : a n < n := by
  sorry

end OeisA117531
