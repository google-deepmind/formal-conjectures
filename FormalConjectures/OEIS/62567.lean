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
# Conjectures associated with A62567

The number whose digits in base 10 are $n$'s digits reversed.

A062567: First multiple of $n$ whose reverse is also divisible by $n$,
or 0 if no such multiple exists.

*References:*
- [A62567](https://oeis.org/A62567)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA62567


open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$,
or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0


@[category API, AMS 11]
lemma a_eq_self (n : ℕ) (hn : n > 0) (h_rev : n ∣ reverse_nat n) : a n = n := by
  unfold a
  rw [if_neg (by omega)]
  have h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n) := ⟨1, ⟨by omega, by rw [one_mul]; exact h_rev⟩⟩
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
lemma reverse_nat_of_lt (k : ℕ) (hk0 : k ≠ 0) (hk10 : k < 10) : reverse_nat k = k := by
  unfold reverse_nat
  rw [Nat.digits_of_lt 10 k hk0 hk10]
  rfl

@[category test, AMS 11]
lemma a_one : a 1 = 1 := by
  apply a_eq_self 1 (by omega) (by rw [reverse_nat_of_lt 1 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by
  apply a_eq_self 2 (by omega) (by rw [reverse_nat_of_lt 2 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by
  apply a_eq_self 3 (by omega) (by rw [reverse_nat_of_lt 3 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_four : a 4 = 4 := by
  apply a_eq_self 4 (by omega) (by rw [reverse_nat_of_lt 4 (by decide) (by decide)])

@[category test, AMS 11]
lemma a_five : a 5 = 5 := by
  apply a_eq_self 5 (by omega) (by rw [reverse_nat_of_lt 5 (by decide) (by decide)])


/--
The number whose digits in base 10 are $n$'s digits reversed.

A062567: First multiple of $n$ whose reverse is also divisible by $n$,
or 0 if no such multiple exists.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/62567.wip.lean#L324"]
theorem target_theorem_0
  (n : ℕ) : 2 ≤ n → (a (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
    sorry

end OeisA62567
