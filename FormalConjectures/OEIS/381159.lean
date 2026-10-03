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
# Numbers whose prime divisors all end in the same digit

Sequence of natural numbers whose prime divisors all end in the same decimal digit (also called
"lopsided" numbers).

*References:*
- [A381159](https://oeis.org/A381159)
-/
open Nat

namespace OeisA381159

/--
Numbers whose prime divisors all end in the same digit.
-/
def condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
Natural numbers whose prime divisors all end in the same decimal digit.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth condition

@[category API, AMS 11]
lemma primeFactors_zero : primeFactors 0 = ∅ := by simp
@[category API, AMS 11]
lemma primeFactors_one : primeFactors 1 = ∅ := by simp

@[category API, AMS 11]
lemma primeFactors_two : primeFactors 2 = {2} := by
  ext x
  simp only [mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hx_prime, hx_div, _⟩
    have : x ≤ 2 := le_of_dvd (by decide) hx_div
    have : 2 ≤ x := hx_prime.two_le
    omega
  · rintro rfl
    exact ⟨prime_two, by decide, by decide⟩

@[category API, AMS 11]
lemma primeFactors_three : primeFactors 3 = {3} := by
  ext x
  simp only [mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hx_prime, hx_div, _⟩
    have : x ≤ 3 := le_of_dvd (by decide) hx_div
    have : 2 ≤ x := hx_prime.two_le
    interval_cases x
    · revert hx_div; decide
    · rfl
  · rintro rfl
    exact ⟨prime_three, by decide, by decide⟩

@[category API, AMS 11]
lemma primeFactors_four : primeFactors 4 = {2} := by
  ext x
  simp only [mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hx_prime, hx_div, _⟩
    have : x ≤ 4 := le_of_dvd (by decide) hx_div
    have : 2 ≤ x := hx_prime.two_le
    interval_cases x
    · rfl
    · revert hx_div; decide
    · revert hx_prime; decide
  · rintro rfl
    exact ⟨prime_two, by decide, by decide⟩

@[category API, AMS 11]
lemma hc0 : condition 0 := by unfold condition; rw [primeFactors_zero]; decide
@[category API, AMS 11]
lemma hc1 : condition 1 := by unfold condition; rw [primeFactors_one]; decide
@[category API, AMS 11]
lemma hc2 : condition 2 := by unfold condition; rw [primeFactors_two]; decide
@[category API, AMS 11]
lemma hc3 : condition 3 := by unfold condition; rw [primeFactors_three]; decide
@[category API, AMS 11]
lemma hc4 : condition 4 := by unfold condition; rw [primeFactors_four]; decide

@[category API, AMS 11]
lemma h0 : Nat.nth condition 0 = 0 := by
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq ⟨hc0, fun x _ => Nat.zero_le x⟩

@[category API, AMS 11]
lemma h1 : Nat.nth condition 1 = 1 := by
  rw [Nat.nth_eq_sInf condition 1]
  exact IsLeast.csInf_eq ⟨⟨hc1, fun k hk => by
    rcases Nat.lt_or_ge k 1 with hk'|hk'
    · interval_cases k
      rw [h0]; decide
    · omega⟩, fun x ⟨_, hx_lt⟩ => by
    have hx_lt0 := hx_lt 0 (by decide); rw [h0] at hx_lt0
    rcases Nat.lt_or_ge x 1 with h|h
    · interval_cases x
    · exact h⟩

@[category API, AMS 11]
lemma h2 : Nat.nth condition 2 = 2 := by
  rw [Nat.nth_eq_sInf condition 2]
  exact IsLeast.csInf_eq ⟨⟨hc2, fun k hk => by
    rcases Nat.lt_or_ge k 2 with hk'|hk'
    · interval_cases k
      · rw [h0]; decide
      · rw [h1]; decide
    · omega⟩, fun x ⟨_, hx_lt⟩ => by
    have hx_lt1 := hx_lt 1 (by decide); rw [h1] at hx_lt1
    rcases Nat.lt_or_ge x 2 with h|h
    · interval_cases x
    · exact h⟩

@[category API, AMS 11]
lemma h3 : Nat.nth condition 3 = 3 := by
  rw [Nat.nth_eq_sInf condition 3]
  exact IsLeast.csInf_eq ⟨⟨hc3, fun k hk => by
    rcases Nat.lt_or_ge k 3 with hk'|hk'
    · interval_cases k
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
    · omega⟩, fun x ⟨_, hx_lt⟩ => by
    have hx_lt2 := hx_lt 2 (by decide); rw [h2] at hx_lt2
    rcases Nat.lt_or_ge x 3 with h|h
    · interval_cases x
    · exact h⟩

@[category API, AMS 11]
lemma h4 : Nat.nth condition 4 = 4 := by
  rw [Nat.nth_eq_sInf condition 4]
  exact IsLeast.csInf_eq ⟨⟨hc4, fun k hk => by
    rcases Nat.lt_or_ge k 4 with hk'|hk'
    · interval_cases k
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
      · rw [h3]; decide
    · omega⟩, fun x ⟨_, hx_lt⟩ => by
    have hx_lt3 := hx_lt 3 (by decide); rw [h3] at hx_lt3
    rcases Nat.lt_or_ge x 4 with h|h
    · interval_cases x
    · exact h⟩

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by unfold a; rw [h0]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by unfold a; rw [h1]

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by unfold a; rw [h2]

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by unfold a; rw [h3]

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by unfold a; rw [h4]

/--
51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end
with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)
-/
@[category textbook, AMS 11]
theorem lopsided_arithmetic_progression :
  answer(sorry) ↔
  ∃ (a d : ℕ),
    -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    2 ≤ a ∧
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), condition (a + i.val * d) := by
  sorry

end OeisA381159
