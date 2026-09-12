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
# Minimized zeroless factorials

$a(n)$ is the smallest positive integer obtained by greedily dividing out factors from $n!$
to avoid the digit zero.

*References:*
- [A374265](https://oeis.org/A374265)
-/
open Nat Finset

namespace OeisA374265

-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
@[category API, AMS 11]
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
The minimized zeroless factorial function $a(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

@[category API, AMS 11]
lemma singleton_min' (x : ℕ) (s : Finset ℕ) (h : s = {x}) (hn : s.Nonempty) : s.min' hn = x := by
  have hmem : x ∈ s := by rw [h]; exact Finset.mem_singleton_self x
  have hle : ∀ y ∈ s, x ≤ y := by
    intro y hy
    rw [h, Finset.mem_singleton] at hy
    rw [hy]
  exact le_antisymm (Finset.min'_le s x hmem) (Finset.le_min' s hn x hle)

@[category API, AMS 11]
lemma digits_lt_10 {n : ℕ} (h : n < 10) (hn : 0 < n) : Nat.digits 10 n = [n] := by
  rw [Nat.digits_def' (by decide : (1 : ℕ) < 10) hn, show n / 10 = 0 from Nat.div_eq_of_lt h,
      Nat.digits_zero]
  rw [Nat.mod_eq_of_lt h]

@[category API, AMS 11]
lemma digits_24 : Nat.digits 10 24 = [4, 2] := by
  rw [Nat.digits_def' (by decide : (1 : ℕ) < 10) (by decide), show 24 / 10 = 2 by rfl]
  rw [digits_lt_10 (by decide) (by decide)]

@[category API, AMS 11]
lemma remove_zeros_1 : remove_zeros 1 = 1 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_2 : remove_zeros 2 = 2 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_6 : remove_zeros 6 = 6 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_24 : remove_zeros 24 = 24 := by
  unfold remove_zeros
  rw [digits_24]
  rfl

@[category API, AMS 11]
lemma reachable_0 : reachable_zeroless_factorials 0 = {1} := rfl

@[category API, AMS 11]
lemma reachable_1 : reachable_zeroless_factorials 1 = {1} := by
  change ({1} : Finset ℕ).biUnion (fun m => {1 * m, remove_zeros (1 * m)}) = {1}
  rw [Finset.singleton_biUnion]
  rw [show 1 * 1 = 1 by rfl, remove_zeros_1]
  exact Finset.pair_eq_singleton 1

@[category API, AMS 11]
lemma reachable_2 : reachable_zeroless_factorials 2 = {2} := by
  change (reachable_zeroless_factorials 1).biUnion (fun m => {2 * m, remove_zeros (2 * m)}) = {2}
  rw [reachable_1, Finset.singleton_biUnion]
  rw [show 2 * 1 = 2 by rfl, remove_zeros_2]
  exact Finset.pair_eq_singleton 2

@[category API, AMS 11]
lemma reachable_3 : reachable_zeroless_factorials 3 = {6} := by
  change (reachable_zeroless_factorials 2).biUnion (fun m => {3 * m, remove_zeros (3 * m)}) = {6}
  rw [reachable_2, Finset.singleton_biUnion]
  rw [show 3 * 2 = 6 by rfl, remove_zeros_6]
  exact Finset.pair_eq_singleton 6

@[category API, AMS 11]
lemma reachable_4 : reachable_zeroless_factorials 4 = {24} := by
  change (reachable_zeroless_factorials 3).biUnion (fun m => {4 * m, remove_zeros (4 * m)}) = {24}
  rw [reachable_3, Finset.singleton_biUnion]
  rw [show 4 * 6 = 24 by rfl, remove_zeros_24]
  exact Finset.pair_eq_singleton 24

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := singleton_min' 1 _ reachable_0 _

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := singleton_min' 1 _ reachable_1 _

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := singleton_min' 2 _ reachable_2 _

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := singleton_min' 6 _ reachable_3 _

@[category test, AMS 11]
theorem a_4 : a 4 = 24 := singleton_min' 24 _ reachable_4 _

/--
Is the sequence $a(n)$ bounded?

The sequence is unbounded because deleting zero digits preserves the base-10 digit sum,
and for $n = 10^k - 1$, every reachable value has digit sum at least $9k$,
which forces $a(10^k - 1) \ge 10^{k-1} \to \infty$.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/google-deepmind/formal-conjectures/blob/ce05cfb9dbe2e5aac6634402ffcc8a38ce368ef7/FormalConjectures/OEIS/374265.lean#L433"]
theorem is_bounded : answer(False) ↔ BddAbove (Set.range a) := by
  sorry

end OeisA374265
