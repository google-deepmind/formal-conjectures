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
import Mathlib.Data.Set.Card

/-!
# VC dimension of a set family

This file defines the VC dimension of a set family as the maximum size of a set it shatters.
-/

variable {α : Type*} {𝒜 ℬ : Set (Set α)} {A B : Set α} {a : α} {m n : ℕ}

variable (𝒜 A) in
/-- A set family `𝒜` shatters a set `A` if restricting `𝒜` to `A` gives rise to all subsets of `A`.
-/
def Shatters : Prop := ∀ ⦃B⦄, B ⊆ A → ∃ C ∈ 𝒜, A ∩ C = B

lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 A) (ha : a ∈ A) : ∃ B ∈ 𝒜, A ∩ B = {a} :=
  hs <| Set.singleton_subset_iff.2 ha

lemma Shatters.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hB ↦ let ⟨u, hu, hut⟩ := h𝒜 hB; ⟨u, h hu, hut⟩

lemma Shatters.mono_right (h : B ⊆ A) (hs : Shatters 𝒜 A) : Shatters 𝒜 B := fun u hu ↦ by
  obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu <| inf_le_of_left_le h⟩

lemma Shatters.exists_superset (h : Shatters 𝒜 A) : ∃ B ∈ 𝒜, A ⊆ B :=
  let ⟨B, hB, hst⟩ := h .rfl; ⟨B, hB, Set.inter_eq_left.1 hst⟩

lemma Shatters.of_forall_subset (h : ∀ B, B ⊆ A → B ∈ 𝒜) : Shatters 𝒜 A :=
  fun B hB ↦ ⟨B, h _ hB, Set.inter_eq_right.2 hB⟩

protected lemma Shatters.nonempty (h : Shatters 𝒜 A) : 𝒜.Nonempty :=
  let ⟨B, hB, _⟩ := h .rfl; ⟨B, hB⟩

@[simp] lemma shatters_empty : Shatters 𝒜 ∅ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨A, hs⟩ B hB ↦ ⟨A, hs, by simpa [eq_comm] using hB⟩⟩

protected lemma Shatters.subset_iff (h : Shatters 𝒜 A) : B ⊆ A ↔ ∃ u ∈ 𝒜, A ∩ u = B :=
  ⟨fun hB ↦ h hB, by rintro ⟨u, _, rfl⟩; exact Set.inter_subset_left⟩

lemma shatters_iff : Shatters 𝒜 A ↔ (A ∩ ·) '' 𝒜 = A.powerset :=
  ⟨fun h ↦ by ext B; simp [h.subset_iff], fun h B hB ↦ h.superset hB⟩

lemma univ_shatters : Shatters .univ A := .of_forall_subset <| by simp

@[simp] lemma shatters_univ : Shatters 𝒜 .univ ↔ 𝒜 = .univ := by
  simp [Shatters, Set.eq_univ_iff_forall]

variable (𝒜 n) in
/-- A set family `𝒜` has VC dimension at most `n` if there are no families `x` of elements indexed
by `[n + 1]` and `A` of sets indexed by `2^[n + 1]` such that `x i ∈ A A ↔ i ∈ A` for all
`i ∈ [n], A ⊆ [n]`. -/
def HasVCDimAtMost : Prop :=
  ∀ (x : Fin (n + 1) → α) (A : Set (Fin (n + 1)) → Set α),
    (∀ s, A s ∈ 𝒜) → ¬ ∀ i s, x i ∈ A s ↔ i ∈ s

lemma HasVCDimAtMost.anti (h𝒜ℬ : 𝒜 ≤ ℬ) (hℬ : HasVCDimAtMost ℬ n) : HasVCDimAtMost 𝒜 n :=
  fun _x _A hA ↦ hℬ _ _ fun _s ↦ h𝒜ℬ <| hA _

lemma HasVCDimAtMost.mono (hmn : m ≤ n) (hm : HasVCDimAtMost 𝒜 m) : HasVCDimAtMost 𝒜 n := by
  rintro x A hA h
  replace hmn : m + 1 ≤ n + 1 := by omega
  exact hm (x ∘ Fin.castLE hmn) (A ∘ Set.image (Fin.castLE hmn)) (by simp [hA]) fun i s ↦
    (h ..).trans <| by simp

@[simp] lemma HasVCDimAtMost.empty : HasVCDimAtMost (∅ : Set (Set α)) n := by simp [HasVCDimAtMost]

lemma hasVCDimAtMost_iff_shatters : HasVCDimAtMost 𝒜 n ↔ ∀ A, Shatters 𝒜 A → A.encard ≤ n where
  mp h𝒜 A hA := by
    by_contra! hn
    sorry
  mpr h𝒜 x A hA h := by
    sorry
