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

public import FormalConjecturesUtil

/-!
# Derangement numbers

The derangement number $a(n)$ counts permutations of $n$ elements with no fixed points.
Its official indexing starts at zero.

*References:*
- [A000166](https://oeis.org/A000166)
-/

@[expose] public section

namespace OeisA166

/-- The number of permutations of $n$ elements with no fixed points. -/
def a (n : ℕ) : ℕ := numDerangements n

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 9 := by decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 44 := by decide

@[category test, AMS 5 11]
theorem a_6 : a 6 = 265 := by decide

/-- The value at index four is the square of three. -/
@[category test, AMS 5 11]
theorem a_4_is_perfect_power : Nat.IsPerfectPower (a 4) := by
  exact ⟨3, 2, by decide, by decide, by decide⟩

/-- The first value covered by the conjecture is not a nontrivial perfect power. -/
@[category test, AMS 5 11]
theorem a_3_not_perfect_power : ¬ Nat.IsPerfectPower (a 3) := by
  rintro ⟨b, k, hb, hk, h⟩
  have hbase : 4 ≤ b ^ 2 := by
    exact pow_le_pow_left' (by omega : 2 ≤ b) 2
  have hexponent : b ^ 2 ≤ b ^ k := pow_le_pow_right' (by omega) (by omega : 2 ≤ k)
  rw [a_3] at h
  omega

/-- The standard two-term recurrence for derangement numbers. -/
@[category API, AMS 5 11]
theorem a_add_two (n : ℕ) : a (n + 2) = (n + 1) * (a n + a (n + 1)) := by
  rfl

/--
"Conjecture: a(n) with n > 2 is a perfect power only for n = 4 with a(4) = 3^2."
— Zhi-Wei Sun, January 9, 2025, [A000166](https://oeis.org/A000166).

For $n>2$, the only perfect power among the derangement numbers is $a(4)=3^2$.
-/
@[category research open, AMS 5 11]
theorem perfect_power : ∀ n : ℕ, 2 < n → Nat.IsPerfectPower (a n) → n = 4 := by
  sorry

end OeisA166
