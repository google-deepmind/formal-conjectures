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

end Finset
