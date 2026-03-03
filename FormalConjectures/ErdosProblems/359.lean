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
# Erdős Problem 359

*Reference:* [erdosproblems.com/359](https://www.erdosproblems.com/359)
-/

namespace Erdos359

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest natural number that
cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k \to \infty$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

/-- Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the
least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k ^ {1 + c} \to 0$
for any $c > 0$. -/
@[category research open, AMS 11]
theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry

-- Helper lemmas for isGoodFor_1_low_values

private lemma A_succ_gt' (A : ℕ → ℕ) (hA : IsGoodFor A 1) (j : ℕ) : A j < A (j + 1) :=
  (hA.2.2 j).1.1

private lemma A_succ_le' (A : ℕ → ℕ) (hA : IsGoodFor A 1) (j k : ℕ)
    (hk : A j < k)
    (hksum : ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → k ≠ ∑ i ∈ Finset.Icc a b, A i) :
    A (j + 1) ≤ k :=
  (hA.2.2 j).2 ⟨hk, hksum⟩

private lemma A_not_sum' (A : ℕ → ℕ) (hA : IsGoodFor A 1) (j a b : ℕ)
    (hsub : Finset.Icc a b ⊆ Finset.Iic j) :
    A (j + 1) ≠ ∑ i ∈ Finset.Icc a b, A i :=
  (hA.2.2 j).1.2 a b hsub

private lemma b_le_of_subset' (a b j : ℕ) (hab : a ≤ b) (hsub : Finset.Icc a b ⊆ Finset.Iic j) :
    b ≤ j :=
  Finset.mem_Iic.mp (hsub (Finset.mem_Icc.mpr ⟨hab, le_refl _⟩))

private lemma icc_subset_iic' (a b j : ℕ) (h : b ≤ j) : Finset.Icc a b ⊆ Finset.Iic j := by
  intro x hx; simp [Finset.mem_Icc, Finset.mem_Iic] at *; omega

private lemma A_val_0' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 0 = 1 := hA.1

private lemma A_val_1' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 1 = 2 := by
  have h0 := A_val_0' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 0 2 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 0 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 0 < A 1 := A_succ_gt' A hA 0
    omega

private lemma A_val_2' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 2 = 4 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 1 4 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 1 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 1 < A 2 := A_succ_gt' A hA 1
    have hne3 : A 2 ≠ 3 := by
      have h := A_not_sum' A hA 1 0 1 (icc_subset_iic' 0 1 1 (by omega))
      simp [h0, h1, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    omega

private lemma A_val_3' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 3 = 5 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 2 5 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 2 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, h2, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 2 < A 3 := A_succ_gt' A hA 2
    omega

private lemma A_val_4' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 4 = 8 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  have h3 := A_val_3' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 3 8 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 3 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, h2, h3, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 3 < A 4 := A_succ_gt' A hA 3
    have hne6 : A 4 ≠ 6 := by
      have h := A_not_sum' A hA 3 1 2 (icc_subset_iic' 1 2 3 (by omega))
      simp [h1, h2, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    have hne7 : A 4 ≠ 7 := by
      have h := A_not_sum' A hA 3 0 2 (icc_subset_iic' 0 2 3 (by omega))
      simp [h0, h1, h2, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    omega

private lemma A_val_5' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 5 = 10 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  have h3 := A_val_3' A hA
  have h4 := A_val_4' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 4 10 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 4 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 4 < A 5 := A_succ_gt' A hA 4
    have hne9 : A 5 ≠ 9 := by
      have h := A_not_sum' A hA 4 2 3 (icc_subset_iic' 2 3 4 (by omega))
      simp [h2, h3, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    omega

private lemma A_val_6' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 6 = 14 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  have h3 := A_val_3' A hA
  have h4 := A_val_4' A hA
  have h5 := A_val_5' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 5 14 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 5 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4, h5, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 5 < A 6 := A_succ_gt' A hA 5
    have hne11 : A 6 ≠ 11 := by
      have h := A_not_sum' A hA 5 1 3 (icc_subset_iic' 1 3 5 (by omega))
      simp [h1, h2, h3, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    have hne12 : A 6 ≠ 12 := by
      have h := A_not_sum' A hA 5 0 3 (icc_subset_iic' 0 3 5 (by omega))
      simp [h0, h1, h2, h3, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    have hne13 : A 6 ≠ 13 := by
      have h := A_not_sum' A hA 5 3 4 (icc_subset_iic' 3 4 5 (by omega))
      simp [h3, h4, Finset.sum_Icc_succ_top, Finset.Icc_self] at h
      exact h
    omega

private lemma A_val_7' (A : ℕ → ℕ) (hA : IsGoodFor A 1) : A 7 = 15 := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  have h3 := A_val_3' A hA
  have h4 := A_val_4' A hA
  have h5 := A_val_5' A hA
  have h6 := A_val_6' A hA
  apply Nat.le_antisymm
  · apply A_succ_le' A hA 6 15 (by omega)
    intro a b hsub
    by_cases hab : a ≤ b
    · have hb := b_le_of_subset' a b 6 hab hsub
      interval_cases b <;> interval_cases a <;>
        simp_all [Finset.sum_Icc_succ_top, h0, h1, h2, h3, h4, h5, h6, Finset.Icc_self]
    · simp [Finset.Icc_eq_empty (by omega)]
  · have hgt : A 6 < A 7 := A_succ_gt' A hA 6
    omega

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then the first few terms of $A$ are $1,2,4,5,8,10,14,15,...$. -/
@[category test, AMS 11]
theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  have h0 := A_val_0' A hA
  have h1 := A_val_1' A hA
  have h2 := A_val_2' A hA
  have h3 := A_val_3' A hA
  have h4 := A_val_4' A hA
  have h5 := A_val_5' A hA
  have h6 := A_val_6' A hA
  have h7 := A_val_7' A hA
  ext x
  simp only [Set.mem_image, Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n <;> simp_all
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact ⟨0, by omega, h0⟩
      | exact ⟨1, by omega, h1⟩
      | exact ⟨2, by omega, h2⟩
      | exact ⟨3, by omega, h3⟩
      | exact ⟨4, by omega, h4⟩
      | exact ⟨5, by omega, h5⟩
      | exact ⟨6, by omega, h6⟩
      | exact ⟨7, by omega, h7⟩

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then it is conjectured that $$a_k ~ \frac{k \log k}{\log \log k}$$. -/
@[category research open, AMS 11]
theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

/--
Known to hold for small cases by exhaustive computation. The first few terms of the sequence starting
at 1 are $1,2,4,5,8,10,14,15,\ldots$, verified by direct computation.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/359", AMS 11]
theorem erdos_359.variants.known_result (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

end Erdos359
