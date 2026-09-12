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
# Numbers $k$ such that $2k-1$ and $2k+1$ are prime powers

Numbers $k$ such that both $2k-1$ and $2k+1$ are prime powers.

*References:*
- [A365416](https://oeis.org/A365416)
-/
open Nat

namespace OeisA365416

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
$a(n)$ is the $n$-th integer $k$ such that $2k-1$ and $2k+1$ are both prime powers.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth condition

@[category API, AMS 11]
lemma isPrimePow_3 : IsPrimePow 3 :=
  ⟨3, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩
@[category API, AMS 11]
lemma isPrimePow_5 : IsPrimePow 5 :=
  ⟨5, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩
@[category API, AMS 11]
lemma isPrimePow_7 : IsPrimePow 7 :=
  ⟨7, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩
@[category API, AMS 11]
lemma isPrimePow_9 : IsPrimePow 9 :=
  ⟨3, 2, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩
@[category API, AMS 11]
lemma isPrimePow_11 : IsPrimePow 11 :=
  ⟨11, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩

@[category API, AMS 11]
lemma not_cond_0 : ¬ condition 0 := by
  intro h
  have : (2 * 0 + 1) = 1 := rfl
  exact not_isPrimePow_one (this ▸ h.right)

@[category API, AMS 11]
lemma not_cond_1 : ¬ condition 1 := by
  intro h
  have : (2 * 1 - 1) = 1 := rfl
  exact not_isPrimePow_one (this ▸ h.left)

@[category API, AMS 11]
lemma cond_2 : condition 2 := by
  have h1 : 2 * 2 - 1 = 3 := rfl
  have h2 : 2 * 2 + 1 = 5 := rfl
  rw [condition, h1, h2]
  exact ⟨isPrimePow_3, isPrimePow_5⟩

@[category API, AMS 11]
lemma cond_3 : condition 3 := by
  have h1 : 2 * 3 - 1 = 5 := rfl
  have h2 : 2 * 3 + 1 = 7 := rfl
  rw [condition, h1, h2]
  exact ⟨isPrimePow_5, isPrimePow_7⟩

@[category API, AMS 11]
lemma cond_4 : condition 4 := by
  have h1 : 2 * 4 - 1 = 7 := rfl
  have h2 : 2 * 4 + 1 = 9 := rfl
  rw [condition, h1, h2]
  exact ⟨isPrimePow_7, isPrimePow_9⟩

@[category API, AMS 11]
lemma cond_5 : condition 5 := by
  have h1 : 2 * 5 - 1 = 9 := rfl
  have h2 : 2 * 5 + 1 = 11 := rfl
  rw [condition, h1, h2]
  exact ⟨isPrimePow_9, isPrimePow_11⟩

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  unfold a
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq (s := setOf condition) ⟨cond_2, fun x hx => by
    rcases Nat.lt_or_ge x 2 with h | h
    · interval_cases x
      · exact (not_cond_0 hx).elim
      · exact (not_cond_1 hx).elim
    · exact h⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  unfold a
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | condition x ∧ ∀ k < 1, Nat.nth condition k < x}) ⟨
    ⟨cond_3, by
      intro k hk
      interval_cases k
      have := a_1
      unfold a at this
      rw [this]
      decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 0 (by decide)
      have := a_1
      unfold a at this
      rw [this] at h0
      exact h0
  ⟩

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  unfold a
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | condition x ∧ ∀ k < 2, Nat.nth condition k < x}) ⟨
    ⟨cond_4, by
      intro k hk
      have h1 := a_1; unfold a at h1
      have h2 := a_2; unfold a at h2
      interval_cases k
      · rw [h1]; decide
      · rw [h2]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 1 (by decide)
      have h2 := a_2; unfold a at h2
      rw [h2] at h0
      exact h0
  ⟩

@[category API, AMS 11]
lemma isPrimePow_13 : IsPrimePow 13 :=
  ⟨13, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩

@[category API, AMS 11]
lemma cond_6 : condition 6 := by
  have h1 : 2 * 6 - 1 = 11 := rfl
  have h2 : 2 * 6 + 1 = 13 := rfl
  rw [condition, h1, h2]
  exact ⟨isPrimePow_11, isPrimePow_13⟩

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  unfold a
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | condition x ∧ ∀ k < 3, Nat.nth condition k < x}) ⟨
    ⟨cond_5, by
      intro k hk
      have h1 := a_1; unfold a at h1
      have h2 := a_2; unfold a at h2
      have h3 := a_3; unfold a at h3
      interval_cases k
      · rw [h1]; decide
      · rw [h2]; decide
      · rw [h3]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 2 (by decide)
      have h3 := a_3; unfold a at h3
      rw [h3] at h0
      exact h0
  ⟩

@[category test, AMS 11]
theorem a_5 : a 5 = 6 := by
  unfold a
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | condition x ∧ ∀ k < 4, Nat.nth condition k < x}) ⟨
    ⟨cond_6, by
      intro k hk
      have h1 := a_1; unfold a at h1
      have h2 := a_2; unfold a at h2
      have h3 := a_3; unfold a at h3
      have h4 := a_4; unfold a at h4
      interval_cases k
      · rw [h1]; decide
      · rw [h2]; decide
      · rw [h3]; decide
      · rw [h4]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 3 (by decide)
      have h4 := a_4; unfold a at h4
      rw [h4] at h0
      exact h0
  ⟩

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), p.Prime ∧ 1 < e ∧ p ^ e = m

/--
According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have
exponent greater than 1.
-/
@[category research open, AMS 11]
theorem only_thirteen :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 :=
by sorry

end OeisA365416
