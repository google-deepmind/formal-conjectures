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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace Finset

/-- The reciprocal sum of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

@[simp]
lemma reciprocalSum_empty : reciprocalSum (∅ : Finset ℕ) = 0 := by
  simp [reciprocalSum]

@[simp]
lemma reciprocalSum_singleton (a : ℕ) : reciprocalSum {a} = (1 : ℝ) / a := by
  simp [reciprocalSum]

/-- Reciprocal sums are nonnegative (using the convention `1/0 = 0` in `ℝ`). -/
lemma reciprocalSum_nonneg (A : Finset ℕ) : 0 ≤ reciprocalSum A := by
  classical
  refine Finset.sum_nonneg fun a _ ↦ div_nonneg zero_le_one (Nat.cast_nonneg _)

lemma reciprocalSum_mono {A B : Finset ℕ} (h : A ⊆ B) :
    reciprocalSum A ≤ reciprocalSum B := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun a _ _ ↦
    div_nonneg zero_le_one (Nat.cast_nonneg _)

lemma reciprocalSum_insert {A : Finset ℕ} {a : ℕ} (h : a ∉ A) :
    reciprocalSum (insert a A) = (1 : ℝ) / a + reciprocalSum A := by
  simp [reciprocalSum, sum_insert h]

lemma reciprocalSum_union_of_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    reciprocalSum (A ∪ B) = reciprocalSum A + reciprocalSum B := by
  simp [reciprocalSum, sum_union h]

/-- If every element is at least `1`, each reciprocal is at most `1`, so the sum is ≤ `#A`. -/
lemma reciprocalSum_le_card {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) :
    reciprocalSum A ≤ A.card := by
  classical
  simpa [reciprocalSum, nsmul_one] using
    sum_le_card_nsmul A (fun a ↦ (1 : ℝ) / a) 1 fun a ha ↦ by
      have hpos : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.succ_le_iff.mp (hA a ha))
      exact (div_le_one hpos).mpr (Nat.one_le_cast.mpr (hA a ha))

/-- Strict monotonicity when a positive reciprocal is added. -/
lemma reciprocalSum_lt_reciprocalSum_insert {A : Finset ℕ} {a : ℕ}
    (h : a ∉ A) (ha : a ≠ 0) :
    reciprocalSum A < reciprocalSum (insert a A) := by
  rw [reciprocalSum_insert h, lt_add_iff_pos_left]
  exact div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha))

/-- Erasing an element subtracts its reciprocal. -/
lemma reciprocalSum_erase {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    reciprocalSum A = (1 : ℝ) / a + reciprocalSum (A.erase a) := by
  classical
  conv_lhs => rw [← insert_erase ha]
  rw [reciprocalSum_insert (by simp [mem_erase])]

/-- A nonzero member forces a strictly positive reciprocal sum. -/
lemma reciprocalSum_pos_of_mem {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) (hne : a ≠ 0) :
    0 < reciprocalSum A := by
  have hpos : 0 < (1 : ℝ) / a :=
    div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne))
  have hle : (1 : ℝ) / a ≤ reciprocalSum A := by
    simpa [reciprocalSum_singleton] using
      reciprocalSum_mono (singleton_subset_iff.mpr ha)
  exact lt_of_lt_of_le hpos hle

/-- Under the convention `1/0 = 0`, the reciprocal sum vanishes iff every element is `0`. -/
lemma reciprocalSum_eq_zero_iff (A : Finset ℕ) :
    reciprocalSum A = 0 ↔ ∀ a ∈ A, a = 0 := by
  classical
  constructor
  · intro h a ha
    by_contra hne
    exact (reciprocalSum_pos_of_mem ha hne).ne' h
  · intro h
    simp only [reciprocalSum]
    exact Finset.sum_eq_zero fun a ha => by
      simp [h a ha]

/-- Filtering to `{0}` yields reciprocal sum `0`. -/
@[simp]
lemma reciprocalSum_filter_eq_zero (A : Finset ℕ) :
    reciprocalSum (A.filter (· = 0)) = 0 :=
  (reciprocalSum_eq_zero_iff _).mpr fun _a ha => (mem_filter.mp ha).2


/-- The reciprocal sum is strictly positive iff some nonzero element is present. -/
lemma reciprocalSum_pos_iff (A : Finset ℕ) :
    0 < reciprocalSum A ↔ ∃ a ∈ A, a ≠ 0 := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    by_contra hne
    have hne' : ∀ a ∈ A, a = 0 := fun a ha => by
      by_contra hne0
      exact hne ⟨a, ha, hne0⟩
    have hz : reciprocalSum A = 0 := (reciprocalSum_eq_zero_iff A).mpr hne'
    exact (ne_of_gt h) hz
  · rintro ⟨a, ha, hne⟩
    exact reciprocalSum_pos_of_mem ha hne

/-- Dropping zeros does not change the reciprocal sum (`1/0 = 0` in `ℝ`). -/
lemma reciprocalSum_filter_ne_zero (A : Finset ℕ) :
    reciprocalSum (A.filter (· ≠ 0)) = reciprocalSum A := by
  classical
  simp only [reciprocalSum]
  rw [sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]



/-- A positive member `a` contributes at least `1/a` to the reciprocal sum. -/
lemma one_div_le_reciprocalSum_of_mem {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (_hpos : 0 < a) :
    (1 : ℝ) / a ≤ reciprocalSum A := by
  simpa [reciprocalSum_singleton] using
    reciprocalSum_mono (singleton_subset_iff.mpr ha)

/-- If `A ⊆ {1, …, x}` is nonempty and `x > 0`, then `∑ 1/a ≥ 1/x`. -/
lemma le_reciprocalSum_of_subset_Icc {A : Finset ℕ} {x : ℕ}
    (hA : A ⊆ Icc 1 x) (hne : A.Nonempty) (_hx : 0 < x) :
    (1 : ℝ) / x ≤ reciprocalSum A := by
  obtain ⟨a, ha⟩ := hne
  have haIcc := mem_Icc.mp (hA ha)
  have hapos : 0 < a := lt_of_lt_of_le (Nat.succ_pos 0) haIcc.1
  have hle : (1 : ℝ) / x ≤ (1 : ℝ) / a :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hapos) (by exact_mod_cast haIcc.2)
  exact hle.trans (one_div_le_reciprocalSum_of_mem ha hapos)

/-- Same lower bound for subsets of `{2, …, x}`. -/
lemma le_reciprocalSum_of_subset_Icc_two {A : Finset ℕ} {x : ℕ}
    (hA : A ⊆ Icc 2 x) (hne : A.Nonempty) (hx : 2 ≤ x) :
    (1 : ℝ) / x ≤ reciprocalSum A := by
  have hsub : A ⊆ Icc 1 x :=
    hA.trans (Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ 2))
  exact le_reciprocalSum_of_subset_Icc hsub hne (by omega)


end Finset
