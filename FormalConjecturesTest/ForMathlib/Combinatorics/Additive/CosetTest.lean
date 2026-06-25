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

import Mathlib
import FormalConjecturesForMathlib.Combinatorics.Additive.Coset

/-!
# Sanity checks for maxCosetDim
-/

open scoped Pointwise

/--
The maximum coset dimension in the entire vector space $V$ is exactly the dimension of $V$.
-/
theorem maxCosetDim_univ (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : maxCosetDim K V (Set.univ : Set V) = Module.finrank K V := by
  dsimp [maxCosetDim]
  apply le_antisymm
  · apply csSup_le
    · use 0
      use ⊥
      simp
    · rintro _ ⟨S, _, rfl⟩
      exact Submodule.finrank_le S.direction
  · apply le_csSup
    · use Module.finrank K V
      rintro _ ⟨S, _, rfl⟩
      exact Submodule.finrank_le S.direction
    · use ⊤
      refine ⟨Set.subset_univ _, ?_⟩
      rw [AffineSubspace.direction_top, finrank_top]

/-- The maximum coset dimension in the empty set $\emptyset$ is $0$. -/
theorem maxCosetDim_empty (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : maxCosetDim K V (∅ : Set V) = 0 := by
  dsimp [maxCosetDim]
  have h : {Module.finrank K S.direction | (S : AffineSubspace K V) (_h : (S : Set V) ⊆ ∅)} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.subset_empty_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have hbot : S = ⊥ := SetLike.ext'_iff.mpr (by simp [hS])
      rw [hbot, AffineSubspace.direction_bot, finrank_bot]
    · rintro rfl
      use ⊥
      simp
  rw [h, csSup_singleton]

/--
If $A \subseteq B$, then the maximum coset dimension achievable in $A$
cannot exceed the maximum coset dimension achievable in $B$.
-/
theorem maxCosetDim_mono (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {A B : Set V} (h : A ⊆ B) :
    maxCosetDim K V A ≤ maxCosetDim K V B := by
  dsimp [maxCosetDim]
  -- We show that any dimension achievable in A is bounded by the supremum in B
  apply csSup_le
  · use 0
    use ⊥
    simp [Set.empty_subset]
  · rintro d ⟨S, hS, rfl⟩
    apply le_csSup
    · -- Prove the set of dimensions in B is bounded above
      use Module.finrank K V
      rintro _ ⟨S', _, rfl⟩
      exact Submodule.finrank_le S'.direction
    · -- The witness S in A is also a witness in B
      use S
      exact ⟨Set.Subset.trans hS h, rfl⟩

/--
If the target set $A$ is already an affine subspace, the function
returns exactly the rank of its direction.
-/
theorem maxCosetDim_affineSubspace (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : AffineSubspace K V) :
    maxCosetDim K V (S : Set V) = Module.finrank K S.direction := by
  dsimp [maxCosetDim]
  apply le_antisymm
  · apply csSup_le
    · use 0
      use ⊥
      simp [Set.empty_subset]
    · rintro _ ⟨S', hS', rfl⟩
      exact Submodule.finrank_mono (AffineSubspace.direction_le hS')
  · apply le_csSup
    · use Module.finrank K V
      rintro _ ⟨S', _, rfl⟩
      exact Submodule.finrank_le S'.direction
    · use S

/--
Similar to the empty set, a set containing exactly one vector should yield
a maximum dimension of 0.
-/
theorem maxCosetDim_singleton (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v : V) : maxCosetDim K V ({v} : Set V) = 0 := by
  dsimp [maxCosetDim]
  have h : {Module.finrank K S.direction | (S : AffineSubspace K V) (_h : (S : Set V) ⊆ {v})} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS, rfl⟩
      obtain rfl | h_nonempty := eq_bot_or_bot_lt S
      · rw [AffineSubspace.direction_bot, finrank_bot]
      · have h_dir : S.direction = ⊥ := by
          apply eq_bot_iff.mpr
          rintro y hy
          have h_coe : (S : Set V) ≠ ∅ := by
            intro h_emp
            apply ne_of_gt h_nonempty
            exact (AffineSubspace.coe_eq_bot_iff S).mp h_emp
          obtain ⟨p, hp⟩ : (S : Set V).Nonempty := Set.nonempty_iff_ne_empty.mpr h_coe
          have hpv : p = v := hS hp
          have hpy : y +ᵥ p ∈ S := AffineSubspace.vadd_mem_of_mem_direction hy hp
          have hpyv : y +ᵥ p = v := hS hpy
          rw [hpv] at hpyv
          change y + v = v at hpyv
          simpa using hpyv
        rw [h_dir, finrank_bot]
    · rintro rfl
      use ⊥
      simp
  rw [h, csSup_singleton]

lemma maxCosetDim_vadd_le (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v : V) (A : Set V) :
    maxCosetDim K V (v +ᵥ A) ≤ maxCosetDim K V A := by
  dsimp [maxCosetDim]
  apply csSup_le
  · use 0
    use ⊥
    simp [Set.empty_subset]
  · rintro d ⟨S, hS, rfl⟩
    apply le_csSup
    · use Module.finrank K V
      rintro _ ⟨S', _, rfl⟩
      exact Submodule.finrank_le S'.direction
    · let f : V ≃ᵃ[K] V := AffineEquiv.constVAdd K V (-v)
      refine ⟨S.map (f : V →ᵃ[K] V), ?_, ?_⟩
      · rw [AffineSubspace.coe_map]
        rintro x ⟨y, hy, rfl⟩
        have h_ya : y ∈ v +ᵥ A := hS hy
        rcases h_ya with ⟨a, ha, rfl⟩
        change -v + (v + a) ∈ A
        rw [neg_add_cancel_left]
        exact ha
      · have hd : (S.map (f : V →ᵃ[K] V)).direction = S.direction := by
          rw [AffineSubspace.map_direction]
          change Submodule.map LinearMap.id S.direction = S.direction
          exact Submodule.map_id S.direction
        rw [hd]

/--
Translating a set by a vector does not change its maximum coset dimension.
-/
theorem maxCosetDim_vadd (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v : V) (A : Set V) :
    maxCosetDim K V (v +ᵥ A) = maxCosetDim K V A := by
  apply le_antisymm
  · exact maxCosetDim_vadd_le K V v A
  · have h := maxCosetDim_vadd_le K V (-v) (v +ᵥ A)
    have h_cancel : -v +ᵥ (v +ᵥ A) = A := by
      ext x
      constructor
      · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
        change -v + (v + a) ∈ A
        rw [neg_add_cancel_left]
        exact ha
      · rintro hx
        use v + x
        constructor
        · exact ⟨x, hx, rfl⟩
        · change -v + (v + x) = x
          rw [neg_add_cancel_left]
    rw [h_cancel] at h
    exact h
