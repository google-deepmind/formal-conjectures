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
# Conjectures associated with A100474

a(1) = 1; a(n) is the smallest integer such that a(n) + a(n-1) has the first n distinct prime factors not used before in this construction.

*References:*
- [A100474](https://oeis.org/A100474)
-/

namespace OeisA100474

/-- The $n$-th triangular number. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The primary defining sequence `a`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod (Nat.nth Nat.Prime) - a (n + 1)

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : Nat.count Nat.Prime 13 = 5 := by decide
  have h2 : Nat.Prime 13 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : Nat.count Nat.Prime 17 = 6 := by decide
  have h2 : Nat.Prime 17 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : Nat.count Nat.Prime 19 = 7 := by decide
  have h2 : Nat.Prime 19 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : Nat.count Nat.Prime 23 = 8 := by decide
  have h2 : Nat.Prime 23 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : Nat.count Nat.Prime 29 = 9 := by decide
  have h2 : Nat.Prime 29 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : Nat.count Nat.Prime 31 = 10 := by decide
  have h2 : Nat.Prime 31 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_eleven : Nat.nth Nat.Prime 11 = 37 := by
  have h1 : Nat.count Nat.Prime 37 = 11 := by decide
  have h2 : Nat.Prime 37 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_twelve : Nat.nth Nat.Prime 12 = 41 := by
  have h1 : Nat.count Nat.Prime 41 = 12 := by decide
  have h2 : Nat.Prime 41 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_thirteen : Nat.nth Nat.Prime 13 = 43 := by
  have h1 : Nat.count Nat.Prime 43 = 13 := by decide
  have h2 : Nat.Prime 43 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
lemma test_a_2 : a 2 = 5 := by
  change (Finset.Ico 0 2).prod (Nat.nth Nat.Prime) - a 1 = 5
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
lemma test_a_3 : a 3 = 380 := by
  change (Finset.Ico 2 5).prod (Nat.nth Nat.Prime) - a 2 = 380
  rw [test_a_2]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
lemma test_a_4 : a 4 = 96197 := by
  change (Finset.Ico 5 9).prod (Nat.nth Nat.Prime) - a 3 = 96197
  rw [test_a_3]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_five, nth_prime_six, nth_prime_seven, nth_prime_eight]
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
lemma test_a_5 : a 5 = 58546472 := by
  change (Finset.Ico 9 14).prod (Nat.nth Nat.Prime) - a 4 = 58546472
  rw [test_a_4]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_nine, nth_prime_ten, nth_prime_eleven, nth_prime_twelve, nth_prime_thirteen]
  rfl

/-- A natural number is a semiprime if it is the product of two prime numbers. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q

/--
After a(2) = 5, is there another prime?
-/
@[category research open, AMS 11]
theorem main_conjecture : answer(sorry) ↔ ∃ n > 2, Nat.Prime (a n) := by
  sorry

/--
What is the next semiprime in the sequence after a(11)?
-/
@[category research open, AMS 11]
theorem next_semiprime :
    answer(sorry) = a (sInf {n : ℕ | 11 < n ∧ IsSemiprime (a n)}) := by
  sorry

end OeisA100474


