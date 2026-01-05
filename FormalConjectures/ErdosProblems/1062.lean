/-
Copyright 2025 The Formal Conjectures Authors.

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
import Mathlib.Topology.Basic

/-!
# Erdős Problem 1062

*Reference:* [erdosproblems.com/1062](https://www.erdosproblems.com/1062)
-/

open Classical Filter
open scoped Topology

namespace Erdos1062

/-- A set `A` of positive integers is fork-free if no element divides two distinct
other elements of `A`. -/
def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

/-- The extremal function from Erdős problem 1062: the largest size of a fork-free subset of
`{1,...,n}`. -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

/-- The interval `[m + 1, 3m + 2]` gives a construction showing that `f n` is asymptotically
at least `⌈2n / 3⌉`. -/
@[category research solved, AMS 11]
theorem erdos_1062.lower_bound (n : ℕ) : ⌈(2 * n / 3 : ℝ)⌉₊ ≤ f n := by
  classical
  set m : ℕ := n / 3
  let A : Finset ℕ := Finset.Icc (m + 1) n

  have h_subset : (A : Set ℕ) ⊆ Set.Icc 1 n := by
    intro x hx
    have hx' : m + 1 ≤ x ∧ x ≤ n := by
      simpa [A, Finset.mem_Icc] using hx
    exact ⟨(Nat.succ_le_succ (Nat.zero_le m)).trans hx'.1, hx'.2⟩

  have h_three_mul_lt (a : ℕ) (ha : a ∈ (A : Set ℕ)) : n < a * 3 := by
    have ha_bounds : m + 1 ≤ a ∧ a ≤ n := by
      simpa [A, Finset.mem_Icc] using ha
    have hmod_lt : n % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
    have h_decomp : n = m * 3 + n % 3 := by
      subst m
      simpa [Nat.mul_comm] using (Nat.div_add_mod' n 3).symm
    have h_lt : n < (m + 1) * 3 := by
      calc
        n = m * 3 + n % 3 := h_decomp
        _ < m * 3 + 3 := by
          have := hmod_lt
          exact add_lt_add_left this _
        _ = (m + 1) * 3 := by
          simp [Nat.add_mul]
    have h_mul : (m + 1) * 3 ≤ a * 3 := Nat.mul_le_mul_right 3 ha_bounds.1
    exact lt_of_lt_of_le h_lt h_mul

  have h_forkfree : ForkFree (A : Set ℕ) := by
    intro a ha
    have ha_bounds : m + 1 ≤ a ∧ a ≤ n := by
      simpa [A, Finset.mem_Icc] using ha
    have ha_pos : 0 < a :=
      Nat.succ_le_iff.mp ((Nat.succ_le_succ (Nat.zero_le m)).trans ha_bounds.1)
    have h_aux :
        ∀ {b},
          b ∈ ({b | b ∈ (A : Set ℕ) \ {a} ∧ a ∣ b} : Set ℕ) →
            b = 2 * a := by
      intro b hb
      rcases hb with ⟨⟨hb_mem, hb_ne⟩, hb_div⟩
      rcases hb_div with ⟨k, rfl⟩
      have hb_bounds : m + 1 ≤ a * k ∧ a * k ≤ n := by
        simpa [A, Finset.mem_Icc] using hb_mem
      have hk_pos : 0 < k := by
        have hpos : 0 < a * k := by
          have : 1 ≤ a * k := (Nat.succ_le_succ (Nat.zero_le m)).trans hb_bounds.1
          exact Nat.succ_le_iff.mp this
        have hpos' : 0 < k * a := by simpa [Nat.mul_comm] using hpos
        exact pos_of_mul_pos_left hpos' ha_pos.le
      have hk_lt_three : k < 3 := by
        have hlt : a * k < a * 3 :=
          lt_of_le_of_lt hb_bounds.2 (h_three_mul_lt a ha)
        exact Nat.lt_of_mul_lt_mul_left hlt
      have hk_le_two : k ≤ 2 := Nat.lt_succ_iff.mp hk_lt_three
      have hk_gt_one : 1 < k := by
        have hk_ge_one : 1 ≤ k := Nat.succ_le_iff.mpr hk_pos
        have hk_ne_one : k ≠ 1 := by
          intro hk_eq
          have : a * k ∈ ({a} : Set ℕ) := by simp [hk_eq]
          exact hb_ne this
        exact lt_of_le_of_ne hk_ge_one hk_ne_one.symm
      have hk_ge_two : 2 ≤ k := Nat.succ_le_iff.mpr hk_gt_one
      have hk_two : k = 2 := le_antisymm hk_le_two hk_ge_two
      simp [hk_two, Nat.mul_comm]
    intro b hb b' hb'
    have hb_eq := h_aux hb
    have hb'_eq := h_aux hb'
    simp [hb_eq, hb'_eq]

  have h_card : ((A : Set ℕ)).ncard = n - m := by
    classical
    have h_card_finset : A.card = n - m := by
      -- `Nat.card_Icc` gives `n + 1 - (m + 1)`
      have h := Nat.card_Icc (m + 1) n
      calc
        A.card = (Finset.Icc (m + 1) n).card := rfl
        _ = n + 1 - (m + 1) := h
        _ = n - m := Nat.add_sub_add_right _ _ _
    simp [Set.ncard_coe_finset, h_card_finset]

  have h_witness :
      ∃ A' ⊆ Set.Icc 1 n, ForkFree A' ∧ A'.ncard = n - m := by
    refine ⟨(A : Set ℕ), h_subset, h_forkfree, h_card⟩

  have h_main : n - m ≤ f n := by
    -- `n - m ≤ n` since `m = n / 3`
    have h_le_n : n - m ≤ n := Nat.sub_le _ _
    exact Nat.le_findGreatest h_le_n h_witness

  have h_ceil_le : ⌈(2 * n / 3 : ℝ)⌉₊ ≤ n - m := by
    refine Nat.ceil_le.mpr ?_
    -- `2 * n / 3 ≤ n - m`
    have hm_le : (3 * m : ℝ) ≤ n := by
      have h_mul_le : m * 3 ≤ n := by
        have h_decomp : n = m * 3 + n % 3 := by
          subst m
          simpa using (Nat.div_add_mod' n 3).symm
        have : m * 3 ≤ m * 3 + n % 3 := Nat.le_add_right _ _
        exact h_decomp ▸ this
      have h' : (m * 3 : ℝ) ≤ n := by exact_mod_cast h_mul_le
      nlinarith
    have h_mul : (2 * n : ℝ) ≤ 3 * (n - m) := by nlinarith
    have h_goal : (2 * n / 3 : ℝ) ≤ (n : ℝ) - m := by nlinarith [h_mul]
    have hm : m ≤ n := Nat.div_le_self _ _
    simpa [Nat.cast_sub hm] using h_goal

  exact h_ceil_le.trans h_main

/-- Lebensold proved that for large `n`, the function `f n` lies between `0.6725 n` and
`0.6736 n`. -/
@[category research solved, AMS 11]
theorem erdos_1062.lebensold_bounds :
    ∀ᶠ n in atTop, (0.6725 : ℝ) * n ≤ f n ∧ f n ≤ (0.6736 : ℝ) * n := by
  sorry

/-- Erdős asked whether the limiting density `f n / n` exists and, if so, whether it is
irrational. -/
@[category research open, AMS 11]
theorem erdos_1062.limit_density :
    (∃ l, Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 l) ∧ Irrational l) ↔ answer(sorry) := by
  sorry

end Erdos1062
