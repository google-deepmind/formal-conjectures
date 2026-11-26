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

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Antichain
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Divisibility antichains of products of powers of two and three

The inductive construction used in the classical two-generator d-completeness result.
-/

@[expose] public section

/--
Every natural number is the sum of a finite divisibility antichain of numbers of the form
$2^a 3^b$. The construction proceeds by strong induction, separating the even and odd cases.
-/
lemma Nat.exists_antichain_powers_two_three (n : ℕ) :
    ∃ s : Finset ℕ, (∀ x ∈ s, ∃ a b : ℕ, x = 2 ^ a * 3 ^ b) ∧
      IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨s, hs, hanti, hsum⟩ := ih m (by omega)
      refine ⟨s.image (2 * ·), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨a, b, rfl⟩ := hs y hy
        exact ⟨a + 1, b, by ring⟩
      · intro x hx y hy hxy hdvd
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        exact hanti hx' hy' (fun h => hxy (by rw [h]))
          (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
      · rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
        calc ∑ x ∈ s, id (2 * x) = ∑ x ∈ s, 2 * id x := rfl
          _ = 2 * s.sum id := (Finset.mul_sum ..).symm
          _ = 2 * m := by rw [hsum]
    · have h1 : 3 ^ Nat.log 3 (2 * m + 1) ≤ 2 * m + 1 :=
        Nat.pow_log_le_self 3 (by omega)
      have h2 : 2 * m + 1 < 3 ^ (Nat.log 3 (2 * m + 1) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) _
      generalize Nat.log 3 (2 * m + 1) = k at h1 h2
      obtain ⟨j, hj⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
      rw [pow_succ] at h2
      obtain ⟨s, hs, hanti, hsum⟩ := ih (m - j) (by omega)
      have hle : ∀ y ∈ s, y ≤ m - j := fun y hy =>
        hsum ▸ Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hy
      have hpos : ∀ y ∈ s, 0 < y := fun y hy => by
        obtain ⟨a, b, rfl⟩ := hs y hy
        positivity
      have hnot : 3 ^ k ∉ s.image (2 * ·) := by
        intro h
        obtain ⟨y, _, hy⟩ := Finset.mem_image.1 h
        omega
      refine ⟨insert (3 ^ k) (s.image (2 * ·)), ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact ⟨0, k, by simp⟩
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨a, b, rfl⟩ := hs y hy
          exact ⟨a + 1, b, by ring⟩
      · rw [Finset.coe_insert]
        refine IsAntichain.insert ?_ ?_ ?_
        · intro x hx y hy hxy hdvd
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
          obtain ⟨x', hx', rfl⟩ := hx
          obtain ⟨y', hy', rfl⟩ := hy
          exact hanti hx' hy' (fun h => hxy (by rw [h]))
            (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
        · intro x hx _ hdvd
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
          obtain ⟨y, _, rfl⟩ := hx
          have : 2 ∣ 3 ^ k := (dvd_mul_right 2 y).trans hdvd
          omega
        · intro x hx _ hdvd
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hle y hy
          have := hpos y hy
          obtain ⟨c, hc⟩ := hdvd
          rcases c with _ | _ | c
          · omega
          · omega
          · have h3 : 3 ^ k * 2 ≤ 3 ^ k * (c + 1 + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            rw [← hc] at h3
            omega
      · rw [Finset.sum_insert hnot, Finset.sum_image (fun x _ y _ h => by simpa using h)]
        have : ∑ x ∈ s, id (2 * x) = 2 * s.sum id := (Finset.mul_sum ..).symm
        simp only [id] at this hsum ⊢
        omega
