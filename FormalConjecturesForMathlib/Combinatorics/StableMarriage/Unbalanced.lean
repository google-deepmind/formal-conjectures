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

public import FormalConjecturesForMathlib.Combinatorics.StableMarriage

/-!
# Stable matching with unequal side sizes

Complete strict preferences for firms and workers. Matchings cover all firms and may leave
workers unmatched. Every partner is preferable to being unmatched.

Reference: B. Pittel, *On Likely Solutions of the Stable Matching Problem with Unequal Numbers
of Men and Women* (2017), https://arxiv.org/abs/1701.08900.
-/

@[expose] public section

namespace StableMarriage.Unbalanced

/-- Complete strict rankings for `n` firms and `m` workers, with smaller ranks preferred. -/
structure Profile (n m : ℕ) where
  /-- Each firm's ranks of workers. -/
  firmRank : Fin n → Equiv.Perm (Fin m)
  /-- Each worker's ranks of firms. -/
  workerRank : Fin m → Equiv.Perm (Fin n)
  deriving Inhabited

instance {n m : ℕ} : Fintype (Profile n m) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)))
    { toFun := fun p ↦ ⟨p.1, p.2⟩
      invFun := fun p ↦ (p.firmRank, p.workerRank)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- A matching assigns every firm a distinct worker. -/
abbrev Matching (n m : ℕ) := Fin n ↪ Fin m

/-- A pair blocks if the firm prefers the worker, and the worker prefers the firm to its
assigned firm, if any. The universal condition is vacuous for an unmatched worker. -/
def IsBlockingPair {n m : ℕ} (p : Profile n m) (μ : Matching n m)
    (i : Fin n) (j : Fin m) : Prop :=
  μ i ≠ j ∧ p.firmRank i j < p.firmRank i (μ i) ∧
    ∀ k, μ k = j → p.workerRank j i < p.workerRank j k

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n m : ℕ} (p : Profile n m) (μ : Matching n m) : Prop :=
  ∀ i j, ¬ IsBlockingPair p μ i j

/-- The number of stable matchings covering all firms. -/
noncomputable def numStableMatchings {n m : ℕ} (p : Profile n m) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n m // IsStable p μ}

instance {n m : ℕ} : MeasurableSpace (Profile n m) := ⊤

/-- The joint law of independent uniform rankings on both sides. -/
noncomputable def uniformProfile (n m : ℕ) : PMF (Profile n m) :=
  PMF.uniformOfFintype (Profile n m)

/-- The first moment of the number of stable matchings. -/
noncomputable def expectedNumStableMatchings (n m : ℕ) : ℝ :=
  ∫ p, (numStableMatchings p : ℝ) ∂((uniformProfile n m).toMeasure)

/-- The second moment of the number of stable matchings, under the same profile law. -/
noncomputable def secondMomentNumStableMatchings (n m : ℕ) : ℝ :=
  ∫ p, (numStableMatchings p : ℝ) ^ 2 ∂((uniformProfile n m).toMeasure)

/-- A balanced profile viewed as a rectangular profile. -/
def ofBalancedProfile {n : ℕ} (p : StableMarriage.Profile n) : Profile n n :=
  ⟨p.manRank, p.womanRank⟩

/-- Blocking agrees with the balanced model when a bijection is viewed as an embedding. -/
theorem isBlockingPair_ofBalancedProfile {n : ℕ} (p : StableMarriage.Profile n)
    (μ : StableMarriage.Matching n) (i j : Fin n) :
    IsBlockingPair (ofBalancedProfile p) μ.toEmbedding i j ↔
      StableMarriage.IsBlockingPair p μ i j := by
  constructor
  · rintro ⟨hne, hi, hj⟩
    exact ⟨hne, hi, hj (μ.symm j) (μ.apply_symm_apply j)⟩
  · rintro ⟨hne, hi, hj⟩
    refine ⟨hne, hi, ?_⟩
    intro k hk
    change μ k = j at hk
    change p.womanRank j i < p.womanRank j k
    simpa only [(μ.eq_symm_apply).2 hk] using hj

/-- Stability agrees with the balanced model on bijective matchings. -/
theorem isStable_ofBalancedProfile {n : ℕ} (p : StableMarriage.Profile n)
    (μ : StableMarriage.Matching n) :
    IsStable (ofBalancedProfile p) μ.toEmbedding ↔ StableMarriage.IsStable p μ := by
  simp only [IsStable, StableMarriage.IsStable, isBlockingPair_ofBalancedProfile]

/-- An empty firm side has a stable empty matching. -/
theorem isStable_zero {m : ℕ} (p : Profile 0 m) (μ : Matching 0 m) : IsStable p μ := by
  intro i
  exact Fin.elim0 i

/-- With no firms there is exactly one stable matching, regardless of the workers. -/
theorem numStableMatchings_zero {m : ℕ} (p : Profile 0 m) : numStableMatchings p = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨default, isStable_zero p default⟩, ?_⟩
  intro μ
  exact Subtype.ext (Subsingleton.elim _ _)

/-- With one firm, stability means assigning its first-choice worker. -/
theorem isStable_one_iff {m : ℕ} (p : Profile 1 (m + 1)) (μ : Matching 1 (m + 1)) :
    IsStable p μ ↔ p.firmRank 0 (μ 0) = 0 := by
  constructor
  · intro hs
    by_contra h
    let j := (p.firmRank 0).symm 0
    have hne : μ 0 ≠ j := by
      intro he
      apply h
      simp [he, j]
    apply hs 0 j
    refine ⟨hne, ?_, ?_⟩
    · simpa [j] using (Fin.pos_iff_ne_zero.mpr h)
    · intro k hk
      have hk0 : k = 0 := Subsingleton.elim _ _
      exact (hne (hk0 ▸ hk)).elim
  · intro h i j hb
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hlt := hb.2.1
    rw [h] at hlt
    exact (not_lt_of_ge (Fin.zero_le _)) hlt

/-- Every nonempty one-firm market has exactly one stable matching. -/
theorem numStableMatchings_one {m : ℕ} (p : Profile 1 (m + 1)) :
    numStableMatchings p = 1 := by
  classical
  let μ₀ : Matching 1 (m + 1) :=
    ⟨fun _ ↦ (p.firmRank 0).symm 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  have hμ₀ : IsStable p μ₀ := (isStable_one_iff p μ₀).mpr (by
    change p.firmRank 0 ((p.firmRank 0).symm 0) = 0
    exact (p.firmRank 0).apply_symm_apply 0)
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨μ₀, hμ₀⟩, ?_⟩
  rintro ⟨μ, hμ⟩
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  apply (p.firmRank 0).injective
  change p.firmRank 0 (μ 0) = p.firmRank 0 ((p.firmRank 0).symm 0)
  simpa only [Equiv.apply_symm_apply] using (isStable_one_iff p μ).mp hμ

/-- The profile distribution has total mass one, including when one side is empty. -/
theorem uniformProfile_univ (n m : ℕ) : (uniformProfile n m).toMeasure Set.univ = 1 := by
  simp

/-- The first moment is one when there is one firm and a nonempty worker side. -/
theorem expectedNumStableMatchings_one (m : ℕ) : expectedNumStableMatchings 1 (m + 1) = 1 := by
  simp [expectedNumStableMatchings, numStableMatchings_one]

/-- The second moment is also one in a nonempty one-firm market. -/
theorem secondMomentNumStableMatchings_one (m : ℕ) :
    secondMomentNumStableMatchings 1 (m + 1) = 1 := by
  simp [secondMomentNumStableMatchings, numStableMatchings_one]

end StableMarriage.Unbalanced
