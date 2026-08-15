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
# Number of digits of n raised to the power of the digital root of n

*References:*
- [A113019](https://oeis.org/A113019)
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace OeisA113019

open Nat

/--
a n is the (Number of digits of n) raised to the power of (the digital root of n),
with appropriate adjustments for $n=0$.
-/
def a (n : ℕ) : ℕ :=
  -- The base: number of digits of n (adjusting n=0 to have 1 digit, like n=1).
  let numDigits : ℕ := (Nat.digits 10 (max 1 n)).length

  -- The exponent: digital root of n. This correctly yields 0 for n=0,
  -- and the standard 1..9 for n>0.
  let digitalRoot : ℕ := if n = 0 then 0 else (n - 1) % 9 + 1

  numDigits ^ digitalRoot

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

/--
$n=1$ and $32$ are fixed points. Are there any others?

Yes: `387420489 = 9 ^ 9` is a third fixed point, so the proposed
classification is false.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a113019-counterexample/blob/dc68e0b55c834b24c9e029525deaa562ae144296/lean/OeisA113019FC.lean#L14-L25"]
theorem conjecture : answer(False) ↔ ∀ n : ℕ, a n = n → n = 1 ∨ n = 32 := by
  change False ↔ ∀ n : ℕ, a n = n → n = 1 ∨ n = 32
  constructor
  · exact False.elim
  · intro h
    have hfixed : a 387420489 = 387420489 := by
      simp [a]
    rcases h 387420489 hfixed with h | h <;> omega

/- ## Classification of all fixed points -/



private lemma a_le_log_pow_nine (n : ℕ) (hn : n ≠ 0) :
    a n ≤ (Nat.log 10 n + 1) ^ 9 := by
  unfold a
  rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hn)]
  rw [Nat.digits_len 10 n (by omega) hn]
  simp only [hn, ite_false]
  exact Nat.pow_le_pow_right (by omega) (by omega)



private lemma succ_pow9_lt_ten_pow_base (d : ℕ) (hd : 10 ≤ d) (hd2 : d ≤ 49) :
    (d + 1) ^ 9 < 10 ^ d := by
  interval_cases d <;> norm_num



private lemma succ_pow9_lt_ten_pow (d : ℕ) (hd : 10 ≤ d) : (d + 1) ^ 9 < 10 ^ d := by
  induction d with
  | zero => omega
  | succ k ih =>
    by_cases hk : k + 1 ≤ 49
    · exact succ_pow9_lt_ten_pow_base (k + 1) hd hk
    · push_neg at hk
      specialize ih (by omega : 10 ≤ k)
      -- Goal: (k + 2) ^ 9 < 10 ^ (k + 1) = 10 * 10 ^ k
      -- Step: (k+2)^9 < 2 * (k+1)^9 < 2 * 10^k ≤ 10 * 10^k
      suffices hsuff : (k + 2) ^ 9 < 2 * (k + 1) ^ 9 by
        calc (k + 2) ^ 9
            < 2 * (k + 1) ^ 9 := hsuff
          _ < 2 * 10 ^ k := by linarith
          _ ≤ 10 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = 10 ^ (k + 1) := by ring
      -- Prove (k+2)^9 < 2 * (k+1)^9 for k ≥ 49
      -- Key: (k+2)*50 ≤ 51*(k+1) for k ≥ 49
      -- So ((k+2)*50)^9 ≤ (51*(k+1))^9
      -- And 51^9 < 2 * 50^9, so (k+2)^9 * 50^9 < 2 * 50^9 * (k+1)^9
      -- Cancel 50^9 to get (k+2)^9 < 2 * (k+1)^9
      have h_ratio : (k + 2) * 50 ≤ 51 * (k + 1) := by omega
      have h_pow : (k + 2) ^ 9 * 50 ^ 9 ≤ 51 ^ 9 * (k + 1) ^ 9 := by
        calc (k + 2) ^ 9 * 50 ^ 9
            = ((k + 2) * 50) ^ 9 := by ring
          _ ≤ (51 * (k + 1)) ^ 9 := Nat.pow_le_pow_left h_ratio 9
          _ = 51 ^ 9 * (k + 1) ^ 9 := by ring
      have h51 : (51 : ℕ) ^ 9 < 2 * 50 ^ 9 := by norm_num
      have hk1_pos : 0 < (k + 1) ^ 9 := by positivity
      have h_combined : (k + 2) ^ 9 * 50 ^ 9 < 2 * 50 ^ 9 * (k + 1) ^ 9 := by
        calc (k + 2) ^ 9 * 50 ^ 9
            ≤ 51 ^ 9 * (k + 1) ^ 9 := h_pow
          _ < (2 * 50 ^ 9) * (k + 1) ^ 9 := by
              exact Nat.mul_lt_mul_of_pos_right h51 hk1_pos
          _ = 2 * 50 ^ 9 * (k + 1) ^ 9 := by ring
      -- (k+2)^9 * 50^9 < (2 * (k+1)^9) * 50^9
      have h_rearranged : (k + 2) ^ 9 * 50 ^ 9 < 2 * (k + 1) ^ 9 * 50 ^ 9 := by linarith
      exact lt_of_mul_lt_mul_right h_rearranged (Nat.zero_le _)



private lemma fixed_point_le (n : ℕ) (h : a n = n) : n ≤ 1000000000 := by
  by_contra h_large
  push_neg at h_large
  have hn : n ≠ 0 := by omega
  have hbound := a_le_log_pow_nine n hn
  rw [h] at hbound
  -- n ≤ (Nat.log 10 n + 1) ^ 9
  have hlog : 9 ≤ Nat.log 10 n := by
    rw [Nat.le_log_iff_pow_le (by omega) hn]
    norm_num; omega
  have hpow_le : 10 ^ (Nat.log 10 n) ≤ n := Nat.pow_log_le_self 10 hn
  by_cases hlog9 : Nat.log 10 n = 9
  · rw [hlog9] at hbound; norm_num at hbound; omega
  · have hlog10 : 10 ≤ Nat.log 10 n := by omega
    have hlt := succ_pow9_lt_ten_pow (Nat.log 10 n) hlog10
    -- (log + 1)^9 < 10^log ≤ n, but n ≤ (log + 1)^9
    omega

/-- For `n ≤ 10^9`, `a n = n` implies `n ∈ {1, 32, 387420489}`.
We case-split on `Nat.log 10 n ∈ {0,...,9}` and `(n-1) % 9 + 1 ∈ {1,...,9}`,
giving 90 candidates `(d+1)^s`, then check consistency. -/


private lemma fixed_point_small :
    ∀ n ≤ 1000000000, a n = n → n = 1 ∨ n = 32 ∨ n = 387420489 := by
  intro n hn ha
  by_cases hn0 : n = 0
  · subst hn0; simp [a] at ha
  unfold a at ha
  rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hn0)] at ha
  simp only [hn0, ite_false] at ha
  rw [Nat.digits_len 10 n (by omega) hn0] at ha
  -- ha : (Nat.log 10 n + 1) ^ ((n - 1) % 9 + 1) = n
  have hlog_ub : Nat.log 10 n < 10 :=
    Nat.log_lt_of_lt_pow hn0 (by norm_num; omega)
  generalize hd : Nat.log 10 n = d at ha hlog_ub
  interval_cases d <;> (
    have hmod_ub : (n - 1) % 9 + 1 ≤ 9 := by omega
    generalize hs : (n - 1) % 9 + 1 = s at ha hmod_ub
    interval_cases s <;> (
      norm_num at ha; subst ha
      first | left; rfl | right; left; rfl | right; right; rfl |
        (exfalso; revert hd hs; decide)
    )
  )

/--
$n=1$ and $32$ and $387420489 = 9^9$ are the only fixed points.
-/
@[category research solved, AMS 11]
theorem three_fixed_points : ∀ n : ℕ, a n = n → n = 1 ∨ n = 32 ∨ n = 387420489 := by
  intro n ha
  exact fixed_point_small n (fixed_point_le n ha) ha

end OeisA113019
