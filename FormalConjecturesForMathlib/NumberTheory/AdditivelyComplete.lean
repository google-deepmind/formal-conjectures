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
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Filter.AtTopBot.Defs

variable {M : Type*} [AddCommMonoid M]

open scoped List

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

/-- If `A ⊆ B`, then `subsetSums A ⊆ subsetSums B`. -/
@[gcongr]
theorem subsetSums_mono {A B : Set M} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B :=
  fun _ ⟨C, hC⟩ => ⟨C, hC.1.trans h, hC.2⟩

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

variable [Preorder M]

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddComplete (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A

/-- If `A ⊆ B` and `A` is complete, then `B` is also complete. -/
@[gcongr]
theorem IsAddComplete.mono {A B : Set M} (h : A ⊆ B) (ha : IsAddComplete A) : IsAddComplete B := by
  filter_upwards [ha] with x hx
  exact (subsetSums_mono h) hx

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddStronglyComplete (A : Set M) : Prop :=
  ∀ ⦃B : Set M⦄, B.Finite → IsAddComplete (A \ B)

/-- A strongly complete set is complete. -/
theorem IsAddStronglyComplete.isAddComplete {A : Set M} (hA : IsAddStronglyComplete A) :
    IsAddComplete A := by simpa using hA Set.finite_empty

/-- If `A ⊆ B` and `A` is strongly complete, then `B` is also strongly complete. -/
theorem IsAddStronglyComplete.mono {A B : Set M} (h : A ⊆ B) (ha : IsAddStronglyComplete A) :
    IsAddStronglyComplete B := fun C hC => (ha hC).mono (by grind)

/-- A sequence `A` is strongly complete if `fun m => A (n + m)` is still complete for all `n`. -/
def IsAddStronglyCompleteNatSeq (A : ℕ → M) : Prop :=
  ∀ n, IsAddComplete (Set.range (fun m => A (n + m)))

/-- A strongly complete sequence is complete. -/
theorem IsAddStronglyCompleteNatSeq.isAddComplete {A : ℕ → M}
    (hA : IsAddStronglyCompleteNatSeq A) :
    IsAddComplete (Set.range A) := by simpa using hA 0

open Classical in
/-- If the range of a sequence `A` is strongly complete, then `A` is strongly complete. -/
theorem IsAddStronglyCompleteNatSeq.of_isAddStronglyComplete {A : ℕ → M}
    (h : IsAddStronglyComplete (.range A)) : IsAddStronglyCompleteNatSeq A :=
  fun n => (h (Finset.finite_toSet _)).mono (A := .range A \ ((Finset.range n).image A))
    (fun _ ⟨⟨y, hy⟩, q⟩ => ⟨y - n, by grind⟩)

/-- If `A` is strongly complete and the preimage of each element is finite, then the range of `A`
is strongly complete. -/
theorem IsAddStronglyCompleteNatSeq.isAddStronglyComplete {A : ℕ → M}
    (h : IsAddStronglyCompleteNatSeq A) (hA : ∀ m, (A ⁻¹' {m}).Finite) :
    IsAddStronglyComplete (.range A) := by
  refine fun B hB => ?_
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (hB.preimage' (fun b _ => hA b)).toFinset
  rw [Set.Finite.toFinset_subset, Finset.coe_range] at hn
  refine (h (n + 1)).mono ?_
  refine fun x ⟨y, hy⟩ => ⟨⟨n + 1 + y, hy⟩, fun hx => ?_⟩
  have : n + 1 + y ∈ Set.Iio n := by grind
  grind

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A
