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
# Reversible multiples $a(3^n) = 10^{3^{n-2}} - 1$ for powers of $3$

First multiple of $n$ whose reverse is also divisible by $n$,
or 0 if no such multiple exists.

*References:*
- [A062567](https://oeis.org/A062567)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA62567


open Nat

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverseNat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

open Classical in
/--
First multiple of $n$ whose reverse is also divisible by $n$,
or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverseNat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0


open Classical in
@[category API, AMS 11]
lemma a_eq_self (n : ℕ) (hn : n > 0) (h_rev : n ∣ reverseNat n) : a n = n := by
  unfold a
  rw [if_neg (by omega)]
  have h_ex : ∃ k, k > 0 ∧ n ∣ reverseNat (k * n) := ⟨1, ⟨by omega, by rw [one_mul]; exact h_rev⟩⟩
  rw [dif_pos h_ex]
  change Nat.find h_ex * n = n
  have hf : Nat.find h_ex = 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨by omega, by rw [one_mul]; exact h_rev⟩, ?_⟩
    intro k hk
    interval_cases k
    simp
  rw [hf, one_mul]

@[category API, AMS 11]
lemma reverseNat_of_lt (k : ℕ) (hk0 : k ≠ 0) (hk10 : k < 10) : reverseNat k = k := by
  unfold reverseNat
  rw [Nat.digits_of_lt 10 k hk0 hk10]
  rfl

@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by
  apply a_eq_self 1 (by omega) (by rw [reverseNat_of_lt 1 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by
  apply a_eq_self 2 (by omega) (by rw [reverseNat_of_lt 2 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_3 : a 3 = 3 := by
  apply a_eq_self 3 (by omega) (by rw [reverseNat_of_lt 3 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_4 : a 4 = 4 := by
  apply a_eq_self 4 (by omega) (by rw [reverseNat_of_lt 4 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_5 : a 5 = 5 := by
  apply a_eq_self 5 (by omega) (by rw [reverseNat_of_lt 5 (by decide) (by decide)])


/--
The conjecture that $a(3^n) = 10^{3^{n-2}} - 1$ for $n > 1$ was shown to be false for $4 < n < 21$
by Farideh Firoozbakht, who conjectured that for all $n > 4$, $a(3^n) \neq 10^{3^{n-2}} - 1$.
This latter conjecture is proved here.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/62567.wip.lean#L324"]
theorem a_three_pow_eq (n : ℕ) :
    2 ≤ n → (a (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
    sorry

end OeisA62567
