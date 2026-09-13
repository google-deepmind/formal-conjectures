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

end Finset
