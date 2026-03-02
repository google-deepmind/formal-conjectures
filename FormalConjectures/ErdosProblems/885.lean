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

/-!
# Erdős Problem 885

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., The factor-difference set of integers. (1997)
- [Ji99] Jiménez-Urroz, J., A note on a conjecture of Erdős and {R}osenfeld. (1999)
- [Br19] Bremner, A., On a problem of Erdős related to common factor differences. (2019)
-/

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Nat Set Finset

namespace Erdos885

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/--
Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that
$|\cap_i D(N_i)| \geq k$?
-/
@[category research open, AMS 11]
theorem erdos_885 : answer(sorry) ↔ ∀ k ≥ 1,
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k := by
  sorry

lemma factorDifferenceSet_10 : factorDifferenceSet 10 = {3, 9} := by
  ext d
  simp only [factorDifferenceSet, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h1, hd⟩
    have ha : a ∈ Finset.filter (· ∣ 10) (Finset.Icc 1 10) := by
      simp only [mem_filter, mem_Icc]
      have : a ∣ 10 := Dvd.intro b h1.symm
      exact ⟨⟨by omega, Nat.le_of_dvd (by decide) this⟩, this⟩
    revert ha h1 hd
    decide
  · rintro (rfl | rfl)
    · exact ⟨2, 5, by decide, by omega⟩
    · exact ⟨1, 10, by decide, by omega⟩

lemma factorDifferenceSet_70 : factorDifferenceSet 70 = {3, 9, 33, 69} := by
  ext d
  simp only [factorDifferenceSet, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h1, hd⟩
    have ha : a ∈ Finset.filter (· ∣ 70) (Finset.Icc 1 70) := by
      simp only [mem_filter, mem_Icc]
      have : a ∣ 70 := Dvd.intro b h1.symm
      exact ⟨⟨by omega, Nat.le_of_dvd (by decide) this⟩, this⟩
    revert ha h1 hd
    decide
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨7, 10, by decide, by omega⟩
    · exact ⟨5, 14, by decide, by omega⟩
    · exact ⟨2, 35, by decide, by omega⟩
    · exact ⟨1, 70, by decide, by omega⟩

lemma factorDifferenceSet_112 : factorDifferenceSet 112 = {6, 9, 11, 24, 54, 111} := by
  ext d
  simp only [factorDifferenceSet, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h1, hd⟩
    have ha : a ∈ Finset.filter (· ∣ 112) (Finset.Icc 1 112) := by
      simp only [mem_filter, mem_Icc]
      have : a ∣ 112 := Dvd.intro b h1.symm
      exact ⟨⟨by omega, Nat.le_of_dvd (by decide) this⟩, this⟩
    revert ha h1 hd
    decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨8, 14, by decide, by omega⟩
    · exact ⟨7, 16, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨4, 28, by decide, by omega⟩
    · exact ⟨2, 56, by decide, by omega⟩
    · exact ⟨1, 112, by decide, by omega⟩

lemma factorDifferenceSet_952 : factorDifferenceSet 952 = {6, 18, 54, 111, 234, 474, 951} := by
  ext d
  simp only [factorDifferenceSet, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h1, hd⟩
    have ha : a ∈ Finset.filter (· ∣ 952) (Finset.Icc 1 952) := by
      simp only [mem_filter, mem_Icc]
      have : a ∣ 952 := Dvd.intro b h1.symm
      exact ⟨⟨by omega, Nat.le_of_dvd (by decide) this⟩, this⟩
    revert ha h1 hd
    decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨28, 34, by decide, by omega⟩
    · exact ⟨14, 68, by decide, by omega⟩
    · exact ⟨17, 56, by decide, by omega⟩
    · exact ⟨8, 119, by decide, by omega⟩
    · exact ⟨4, 238, by decide, by omega⟩
    · exact ⟨2, 476, by decide, by omega⟩
    · exact ⟨1, 952, by decide, by omega⟩

lemma factorDifferenceSet_3240 : factorDifferenceSet 3240 = {6, 14, 21, 33, 34, 38, 46, 54, 63, 66, 78, 81, 102, 111, 142, 153, 198, 207, 261, 316, 351, 401, 534, 642, 806, 1077, 1618, 3239} := by
  ext d
  simp only [factorDifferenceSet, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, h1, hd⟩
    have ha : a ∈ Finset.filter (· ∣ 3240) (Finset.Icc 1 3240) := by
      simp only [mem_filter, mem_Icc]
      have : a ∣ 3240 := Dvd.intro b h1.symm
      exact ⟨⟨by omega, Nat.le_of_dvd (by decide) this⟩, this⟩
    revert ha h1 hd
    decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨54, 60, by decide, by omega⟩
    · exact ⟨40, 81, by decide, by omega⟩
    · exact ⟨45, 72, by decide, by omega⟩
    · exact ⟨36, 90, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨30, 108, by decide, by omega⟩
    · exact ⟨36, 90, by decide, by omega⟩
    · exact ⟨27, 120, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨24, 135, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨20, 162, by decide, by omega⟩
    · exact ⟨24, 135, by decide, by omega⟩
    · exact ⟨18, 180, by decide, by omega⟩
    · exact ⟨15, 216, by decide, by omega⟩
    · exact ⟨12, 270, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩
    · exact ⟨10, 324, by decide, by omega⟩
    · exact ⟨9, 360, by decide, by omega⟩
    · exact ⟨8, 405, by decide, by omega⟩
    · exact ⟨6, 540, by decide, by omega⟩
    · exact ⟨5, 648, by decide, by omega⟩
    · exact ⟨4, 810, by decide, by omega⟩
    · exact ⟨3, 1080, by decide, by omega⟩
    · exact ⟨2, 1620, by decide, by omega⟩
    · exact ⟨1, 3240, by decide, by omega⟩
    · exact ⟨0, 0, by decide, by decide⟩

/--
Erdős and Rosenfeld [ErRo97] proved this is true for $k=2$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/YOUR_PR_NUMBER", AMS 11]
theorem erdos_885.variants.k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  use {10, 70}
  refine ⟨by decide, by decide, ?_⟩
  have : ⋂ n ∈ ({10, 70} : Finset ℕ), factorDifferenceSet n = {3, 9} := by
    ext x
    simp only [mem_iInter, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro h
      have h10 : x ∈ factorDifferenceSet 10 := h 10 (by tauto)
      rw [factorDifferenceSet_10] at h10
      exact h10
    · rintro hx i hi
      rcases hi with rfl | rfl
      · rw [factorDifferenceSet_10]; exact hx
      · rw [factorDifferenceSet_70]
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  rw [this]
  have h2 : ({3, 9} : Set ℕ).ncard = 2 := by rfl
  rw [h2]
  exact le_refl 2

/--
Jiménez-Urroz [Ji99] proved this for $k=3$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/YOUR_PR_NUMBER", AMS 11]
theorem erdos_885.variants.k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  use {112, 952, 3240}
  refine ⟨by decide, by decide, ?_⟩
  have : ⋂ n ∈ ({112, 952, 3240} : Finset ℕ), factorDifferenceSet n = {6, 54, 111} := by
    ext x
    simp only [mem_iInter, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro h
      have h112 : x ∈ factorDifferenceSet 112 := h 112 (by tauto)
      rw [factorDifferenceSet_112] at h112
      exact h112
    · rintro hx i hi
      rcases hi with rfl | rfl | rfl
      · rw [factorDifferenceSet_112]; exact hx
      · rw [factorDifferenceSet_952]
        rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [factorDifferenceSet_3240]
        rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  rw [this]
  have h3 : ({6, 54, 111} : Set ℕ).ncard = 3 := by rfl
  rw [h3]
  exact le_refl 3

/--
Bremner [Br19] proved this for $k=4$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  sorry

end Erdos885
