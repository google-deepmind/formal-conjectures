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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Filter.AtTopBot.Defs

variable {M : Type*} [AddCommMonoid M]

open scoped List

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, B.toSet ⊆ A ∧ n = ∑ i ∈ B, i}

/-- If `A ⊆ B`, then `subsetSums A ⊆ subsetSums B`. -/
@[gcongr]
theorem subsetSums_mono {A B : Set M} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B :=
  fun _ ⟨C, hC⟩ => ⟨C, hC.1.trans h, hC.2⟩

/-- The set of subset sums of a sequence `ℕ → M`. -/
def subseqSums (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, B.toSet.InjOn A ∧ n = ∑ i ∈ B, A i}

/-- The set of subset sums of a sequence is `ℕ → M` is equal to the set of subset sums of its
range. -/
theorem subseqSums_eq_subsetSums (A : ℕ → M) : subsetSums (Set.range A) = subseqSums A := by
  ext x
  classical
  refine ⟨fun ⟨C, hC⟩ => ?_, fun ⟨C, hC⟩ => ?_⟩
  · choose! n hn using fun i (hi : i ∈ C) => hC.1 hi
    exact ⟨Finset.image n C, fun i hi j hj hij => by aesop, hC.2.trans
      ((Finset.sum_image fun i hi j hj hij => by grind).trans (by aesop)).symm⟩
  · exact ⟨C.image A, by grind, hC.2.trans (by simp [Finset.sum_image hC.1])⟩

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddComplete (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A

/-- If `A ⊆ B` and `A` is complete, then `B` is also complete. -/
@[gcongr]
theorem isAddComplete_mono {A B : Set M} (h : A ⊆ B) (ha : IsAddComplete A) : IsAddComplete B := by
  filter_upwards [ha] with x hx
  exact (subsetSums_mono h) hx

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddStronglyComplete (A : Set M) : Prop :=
  ∀ {B : Set M}, B.Finite → IsAddComplete (A \ B)

/-- A strongly complete set is complete. -/
theorem IsAddStronglyComplete.isAddComplete {A : Set M} (hA : IsAddStronglyComplete A) :
    IsAddComplete A := by simpa using hA Set.finite_empty

/-- If `A ⊆ B` and `A` is strongly complete, then `B` is also strongly complete. -/
theorem isAddStronglyComplete_mono {A B : Set M} (h : A ⊆ B) (ha : IsAddStronglyComplete A) :
    IsAddStronglyComplete B := fun hC => isAddComplete_mono (by grind) (ha hC)

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
distinct terms of `A`. -/
def IsAddCompleteNatSeq (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums A

/-- A sequence `A` is complete iff its range is complete. -/
theorem isAddCompleteNatSeq_iff_isAddCompleteNatSeq (A : ℕ → M) : IsAddComplete (.range A) ↔
    IsAddCompleteNatSeq A where
  mp h := by filter_upwards [h] with x hx; simp [← subseqSums_eq_subsetSums A, hx]
  mpr h := by filter_upwards [h] with x hx; simp [subseqSums_eq_subsetSums A, hx]

/-- A sequence `A` is strongly complete if `fun m => A (n + m)` is still complete for all `n`. -/
def IsAddStronglyCompleteNatSeq (A : ℕ → M) : Prop :=
  ∀ n, IsAddCompleteNatSeq (fun m => A (n + m))

/-- A strongly complete sequence is complete. -/
theorem IsAddStronglyCompleteNatSeq.isAddCompleteNatSeq {A : ℕ → M}
    (hA : IsAddStronglyCompleteNatSeq A) :
    IsAddCompleteNatSeq A := by simpa using hA 0

open Classical in
/-- If the range of a sequence `A` is strongly complete, then `A` is strongly complete. -/
theorem IsAddStronglyComplete.isAddStronglyCompleteNatSeq {A : ℕ → M}
    (h : IsAddStronglyComplete (.range A)) : IsAddStronglyCompleteNatSeq A :=
  fun n => (isAddCompleteNatSeq_iff_isAddCompleteNatSeq (fun m => A (n + m))).1
    (isAddComplete_mono (A := .range A \ ((Finset.range n).image A)) (fun _ ⟨⟨y, hy⟩, q⟩ =>
    ⟨y - n, by grind⟩) (h (Finset.finite_toSet _)))

/-- If `A` is strongly complete and its range is infinite, then the range of `A` is strongly
complete.-/
theorem IsAddStronglyCompleteNatSeq.isAddStronglyComplete  {A : ℕ → M}
    (h : IsAddStronglyCompleteNatSeq A) (hA : (Set.range A).Infinite) :
    IsAddStronglyComplete (.range A) := by
  sorry

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A
