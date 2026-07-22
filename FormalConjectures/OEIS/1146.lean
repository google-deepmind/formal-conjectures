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
# a(n) = 2^(2^n)

a(n) = 2^(2^n).

*References:*
- [A001146](https://oeis.org/A001146)
-/

namespace OeisA001146

/--
The primary defining sequence `a`.
a(n) = 2^(2^n).
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n)

@[category test, AMS 11]
lemma test_a_0 : a 0 = 2 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 16 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 256 := by rfl

@[category API, AMS 11]
lemma n_add_two_le_two_pow (n : ℕ) (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · decide
  · calc
      k + 1 + 2 = k + 2 + 1 := by omega
      _ ≤ 2 ^ k + 1 := by exact Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := by
        apply Nat.add_le_add_left
        apply Nat.one_le_pow'
      _ = 2 ^ (k + 1) := by ring

/--
The forward direction: if k = a(n) for n >= 2, then k^4 - 1 divides 2^k - 1.
-/
@[category research solved, AMS 11]
theorem divisibility_fact (n : ℕ) (hn : 2 ≤ n) : (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ) := by
  let m := 2 ^ (2 ^ n - (n + 2))
  have h_exp : 2 ^ 2 ^ n = (2 ^ n * 4) * m := by
    dsimp [m]
    have h_four : 2 ^ n * 4 = 2 ^ (n + 2) := by
      calc
        2 ^ n * 4 = 2 ^ n * 2 ^ 2 := by rfl
        _ = 2 ^ (n + 2) := by rw [← pow_add]
    rw [h_four]
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_cancel' (n_add_two_le_two_pow n hn)).symm
  have H2 : 2 ^ a n = (a n ^ 4) ^ m := by
    dsimp [a, m]
    rw [← pow_mul, ← pow_mul]
    rw [← mul_assoc]
    congr 1
  rw [H2]
  exact Nat.sub_one_dvd_pow_sub_one (a n ^ 4) m

/--
I conjecture that { a(n) ; n>1 } are the numbers such that n^4-1 divides 2^n-1, intersection of A247219 and A247165. - M. F. Hasler, Jul 25 2015
This formalizes the reverse direction.
-/
@[category research open, AMS 11]
theorem conjecture2 :
  ∀ k : ℕ, ((k^4 - 1) : ℕ) ∣ (2^k - 1 : ℕ) → k > 1 → ∃ n : ℕ, 2 ≤ n ∧ k = a n := by
  sorry

end OeisA001146
