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
# Maximality of $k = 43$ with restricted digit counts in bases $3 \le b < k$

Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

The sequence Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.

*References:*
- [A306424](https://oeis.org/A306424)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

@[expose] public section

namespace OeisA306424


open List Finset Nat

/--
Numbers $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.
-/
def Condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The $n$-th number $k$ such that the base $b$ expansion of $k$ for each
$b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth Condition

@[category test, AMS 11]
lemma Condition_lt_four {k : ℕ} (hk : k ≤ 3) : Condition k := by
  intro b ⟨hb1, hb2⟩
  omega

@[category test, AMS 11]
lemma Condition_zero : Condition 0 := Condition_lt_four (by omega)

@[category test, AMS 11]
lemma Condition_one : Condition 1 := Condition_lt_four (by omega)

@[category test, AMS 11]
lemma Condition_two : Condition 2 := Condition_lt_four (by omega)

@[category test, AMS 11]
lemma Condition_three : Condition 3 := Condition_lt_four (by omega)

@[category test, AMS 11]
lemma Condition_four : Condition 4 := by
  intro b ⟨hb1, hb2⟩
  have hb : b = 3 := by omega
  subst hb
  decide

@[category test, AMS 11]
lemma Condition_five : Condition 5 := by
  intro b ⟨hb1, hb2⟩
  interval_cases b
  · decide
  · decide


@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by
  change Nat.nth Condition 1 = 1
  rw [Nat.nth_eq_sInf]
  have h0 : Nat.nth Condition 0 = 0 := Nat.nth_zero_of_zero Condition_zero
  have hmem : 1 ∈ {x | Condition x ∧ ∀ k < 1, Nat.nth Condition k < x} := by
    refine ⟨Condition_one, fun k hk => ?_⟩
    interval_cases k
    rw [h0]
    exact zero_lt_one
  have h_inf_mem := Nat.sInf_mem ⟨1, hmem⟩
  have h_gt_zero := h_inf_mem.2 0 (by omega)
  rw [h0] at h_gt_zero
  have h_le_one : sInf {x | Condition x ∧ ∀ k < 1, Nat.nth Condition k < x} ≤ 1 :=
    csInf_le (OrderBot.bddBelow _) hmem
  omega

@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by
  change Nat.nth Condition 2 = 2
  rw [Nat.nth_eq_sInf]
  have h0 : Nat.nth Condition 0 = 0 := Nat.nth_zero_of_zero Condition_zero
  have h1 : Nat.nth Condition 1 = 1 := a_1
  have hmem : 2 ∈ {x | Condition x ∧ ∀ k < 2, Nat.nth Condition k < x} := by
    refine ⟨Condition_two, fun k hk => ?_⟩
    interval_cases k
    · rw [h0]; exact zero_lt_two
    · rw [h1]; exact one_lt_two
  have h_inf_mem := Nat.sInf_mem ⟨2, hmem⟩
  have h_gt_one := h_inf_mem.2 1 (by omega)
  rw [h1] at h_gt_one
  have h_le_two : sInf {x | Condition x ∧ ∀ k < 2, Nat.nth Condition k < x} ≤ 2 :=
    csInf_le (OrderBot.bddBelow _) hmem
  omega

@[category test, AMS 11]
lemma a_3 : a 3 = 3 := by
  change Nat.nth Condition 3 = 3
  rw [Nat.nth_eq_sInf]
  have h0 : Nat.nth Condition 0 = 0 := Nat.nth_zero_of_zero Condition_zero
  have h1 : Nat.nth Condition 1 = 1 := a_1
  have h2 : Nat.nth Condition 2 = 2 := a_2
  have hmem : 3 ∈ {x | Condition x ∧ ∀ k < 3, Nat.nth Condition k < x} := by
    refine ⟨Condition_three, fun k hk => ?_⟩
    interval_cases k
    · rw [h0]; omega
    · rw [h1]; omega
    · rw [h2]; omega
  have h_inf_mem := Nat.sInf_mem ⟨3, hmem⟩
  have h_gt_two := h_inf_mem.2 2 (by omega)
  rw [h2] at h_gt_two
  have h_le_three : sInf {x | Condition x ∧ ∀ k < 3, Nat.nth Condition k < x} ≤ 3 :=
    csInf_le (OrderBot.bddBelow _) hmem
  omega

@[category test, AMS 11]
lemma a_4 : a 4 = 4 := by
  change Nat.nth Condition 4 = 4
  rw [Nat.nth_eq_sInf]
  have h0 : Nat.nth Condition 0 = 0 := Nat.nth_zero_of_zero Condition_zero
  have h1 : Nat.nth Condition 1 = 1 := a_1
  have h2 : Nat.nth Condition 2 = 2 := a_2
  have h3 : Nat.nth Condition 3 = 3 := a_3
  have hmem : 4 ∈ {x | Condition x ∧ ∀ k < 4, Nat.nth Condition k < x} := by
    refine ⟨Condition_four, fun k hk => ?_⟩
    interval_cases k
    · rw [h0]; omega
    · rw [h1]; omega
    · rw [h2]; omega
    · rw [h3]; omega
  have h_inf_mem := Nat.sInf_mem ⟨4, hmem⟩
  have h_gt_three := h_inf_mem.2 3 (by omega)
  rw [h3] at h_gt_three
  have h_le_four : sInf {x | Condition x ∧ ∀ k < 4, Nat.nth Condition k < x} ≤ 4 :=
    csInf_le (OrderBot.bddBelow _) hmem
  omega

@[category test, AMS 11]
lemma a_5 : a 5 = 5 := by
  change Nat.nth Condition 5 = 5
  rw [Nat.nth_eq_sInf]
  have h0 : Nat.nth Condition 0 = 0 := Nat.nth_zero_of_zero Condition_zero
  have h1 : Nat.nth Condition 1 = 1 := a_1
  have h2 : Nat.nth Condition 2 = 2 := a_2
  have h3 : Nat.nth Condition 3 = 3 := a_3
  have h4 : Nat.nth Condition 4 = 4 := a_4
  have hmem : 5 ∈ {x | Condition x ∧ ∀ k < 5, Nat.nth Condition k < x} := by
    refine ⟨Condition_five, fun k hk => ?_⟩
    interval_cases k
    · rw [h0]; omega
    · rw [h1]; omega
    · rw [h2]; omega
    · rw [h3]; omega
    · rw [h4]; omega
  have h_inf_mem := Nat.sInf_mem ⟨5, hmem⟩
  have h_gt_four := h_inf_mem.2 4 (by omega)
  rw [h4] at h_gt_four
  have h_le_five : sInf {x | Condition x ∧ ∀ k < 5, Nat.nth Condition k < x} ≤ 5 :=
    csInf_le (OrderBot.bddBelow _) hmem
  omega


/--
Conjecture: The sequence is finite, with 43 being the last term.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/306424.wip.lean#L276"]
theorem forty_three_is_max : Condition 43 ∧ ∀ k : ℕ, 43 < k → ¬Condition k := by
    sorry

end OeisA306424
