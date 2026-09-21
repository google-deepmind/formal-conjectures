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
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.WellFounded

@[expose] public section

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

open scoped Classical in
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

/-! ### Sequences whose partial sums are dominated by the next term

If `A : ℕ → ℕ` is strictly increasing from index `n₀` on and `A 0 + ⋯ + A (m - 1) ≤ A (m + 1)`
for `m ≥ n₀`, then removing infinitely many terms from `A` destroys completeness. This is the
argument of Graham [Gr64d] for the sequence `n ↦ fib n - (-1) ^ n`: once three terms
`A m₁ < A m₂ < A m` are removed, the remaining terms below `A (m + 1)` sum to at most
`A (m + 1) - 2`, so `A (m + 1) - 1` is not a sum of distinct remaining terms. -/

/-- Let `A : ℕ → ℕ` be strictly increasing from index `n₀` on, with
`A 0 + ⋯ + A (m - 1) ≤ A (m + 1)` for all `m ≥ n₀`. Then `Set.range A \ B` is not complete for
any infinite `B ⊆ Set.range A`. -/
theorem not_isAddComplete_range_diff_of_sum_range_le {A : ℕ → ℕ} {n₀ : ℕ}
    (hA : StrictMono fun k => A (n₀ + k))
    (hsum : ∀ m, n₀ ≤ m → ∑ i ∈ Finset.range m, A i ≤ A (m + 1))
    {B : Set ℕ} (hB : B ⊆ Set.range A) (hB' : B.Infinite) :
    ¬ IsAddComplete (Set.range A \ B) := by
  -- Infinitely many indices `m` have `A m ∈ B`.
  have hpre : (A ⁻¹' B).Infinite := by
    intro hfin
    refine hB' <| (hfin.image A).subset fun b hb => ?_
    obtain ⟨m, rfl⟩ := hB hb
    exact ⟨m, hb, rfl⟩
  -- `A` grows at least linearly from `n₀` on.
  have hlin : ∀ k, n₀ ≤ k → k - n₀ ≤ A k := fun k hk => by
    have := hA.id_le (k - n₀)
    rwa [show n₀ + (k - n₀) = k by omega] at this
  have hlt : ∀ i j, n₀ ≤ i → n₀ ≤ j → (A i < A j ↔ i < j) := by
    intro i j hi hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [hA.lt_iff_lt]
    omega
  rw [IsAddComplete, Filter.not_eventually, Filter.frequently_atTop]
  intro N
  -- Three removed indices `n₀ < m₁ < m₂ < m`, with `m₁` large.
  obtain ⟨m₁, hm₁B, hm₁⟩ := hpre.exists_gt (n₀ + N)
  obtain ⟨m₂, hm₂B, hm₂⟩ := hpre.exists_gt m₁
  obtain ⟨m, hmB, hm⟩ := hpre.exists_gt m₂
  have hAm₁ := hlin m₁ (by omega)
  have hAm₂ := hlin m₂ (by omega)
  have hAm := hlin (m + 1) (by omega)
  refine ⟨A (m + 1) - 1, by omega, ?_⟩
  rintro ⟨C, hC, hsumC⟩
  -- Every element of `C` is `A i` with `i < m`, `A i ≠ A m₁` and `A i ≠ A m₂`.
  set S := (Finset.range m).filter (fun i => A i ≠ A m₁ ∧ A i ≠ A m₂) with hS
  have hCsub : C ⊆ S.image A := by
    intro c hc
    obtain ⟨⟨i, rfl⟩, hcB⟩ := hC hc
    have hle : A i ≤ ∑ j ∈ C, j :=
      Finset.single_le_sum (f := fun j => j) (fun _ _ => Nat.zero_le _) hc
    have hi : i < m := by
      by_contra hcon
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · obtain rfl : i = m := by omega
        exact hcB hmB
      · have : A (m + 1) ≤ A i :=
          not_lt.1 fun h' => by have := (hlt i (m + 1) (by omega) (by omega)).1 h'; omega
        omega
    refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_, ?_⟩, rfl⟩
    · rintro h; exact hcB (h ▸ hm₁B)
    · rintro h; exact hcB (h ▸ hm₂B)
  have h1 : ∑ j ∈ C, j ≤ ∑ i ∈ S, A i :=
    (Finset.sum_le_sum_of_subset hCsub).trans
      (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _)
  -- `S` avoids `m₁` and `m₂`, whose terms are at least `1` each.
  have h2 : ∑ i ∈ S, A i + A m₁ + A m₂ ≤ ∑ i ∈ Finset.range m, A i := by
    have hsub : S ⊆ ((Finset.range m).erase m₁).erase m₂ := by
      intro i hi
      obtain ⟨hi, h₁, h₂⟩ := Finset.mem_filter.1 hi
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hi⟩⟩
      · rintro rfl; exact h₂ rfl
      · rintro rfl; exact h₁ rfl
    have e1 := Finset.add_sum_erase (Finset.range m) A (Finset.mem_range.2 (by omega : m₁ < m))
    have e2 := Finset.add_sum_erase ((Finset.range m).erase m₁) A
      (Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega : m₂ < m)⟩)
    have := Finset.sum_le_sum_of_subset (f := A) hsub
    omega
  have := hsum m (by omega)
  omega
