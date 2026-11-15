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
# Stable partners and reassignment of preference lists

A pair is stable if it occurs in at least one stable matching. Shuffling preference lists changes
which agent owns a list, while preserving the candidate names and their order within that list.

Reference: S. Mauras, *Analysis of Random Models for Stable Matchings* (2021), Section 5.8,
https://www.irif.fr/~mauras/thesis/thesis.pdf.
-/

@[expose] public section

namespace StableMarriage

/-- A man and woman are a stable pair if some stable matching pairs them. -/
def IsStablePair {n : ℕ} (p : Profile n) (m w : Fin n) : Prop :=
  ∃ μ : Matching n, IsStable p μ ∧ μ m = w

/-- The different women a man receives across all stable matchings. -/
noncomputable def manStablePartners {n : ℕ} (p : Profile n) (m : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsStablePair p m)

/-- The different men a woman receives across all stable matchings. -/
noncomputable def womanStablePartners {n : ℕ} (p : Profile n) (w : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun m ↦ IsStablePair p m w)

/-- The number of distinct stable pairs, counting each pair once. -/
noncomputable def numStablePairs {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact (Finset.univ.filter fun q : Fin n × Fin n ↦ IsStablePair p q.1 q.2).card

@[simp]
theorem mem_manStablePartners {n : ℕ} (p : Profile n) (m w : Fin n) :
    w ∈ manStablePartners p m ↔ IsStablePair p m w := by
  classical
  simp [manStablePartners]

@[simp]
theorem mem_womanStablePartners {n : ℕ} (p : Profile n) (m w : Fin n) :
    m ∈ womanStablePartners p w ↔ IsStablePair p m w := by
  classical
  simp [womanStablePartners]

/-- Independently reassign the men's lists by `σ` and the women's lists by `τ`.
The permutations act only on the owners, not on the candidates within a list. -/
def shuffle {n : ℕ} (p : Profile n) (σ τ : Equiv.Perm (Fin n)) : Profile n :=
  ⟨fun m ↦ p.manRank (σ m), fun w ↦ p.womanRank (τ w)⟩

@[simp]
theorem shuffle_refl {n : ℕ} (p : Profile n) :
    shuffle p (Equiv.refl _) (Equiv.refl _) = p := by
  rfl

@[simp]
theorem shuffle_manRank {n : ℕ} (p : Profile n) (σ τ : Equiv.Perm (Fin n)) (m w : Fin n) :
    (shuffle p σ τ).manRank m w = p.manRank (σ m) w := by
  rfl

@[simp]
theorem shuffle_womanRank {n : ℕ} (p : Profile n) (σ τ : Equiv.Perm (Fin n)) (m w : Fin n) :
    (shuffle p σ τ).womanRank w m = p.womanRank (τ w) m := by
  rfl

/-- Mean number of stable pairs over two independent uniform owner permutations. -/
noncomputable def expectedNumStablePairsAfterShuffle {n : ℕ} (p : Profile n) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
    (numStablePairs (shuffle p σ τ) : ℝ)) / (Nat.factorial n : ℝ) ^ 2

/-- An empty market has no stable pairs. -/
@[simp]
theorem numStablePairs_zero (p : Profile 0) : numStablePairs p = 0 := by
  simp [numStablePairs]

/-- In a singleton market the unique pair is stable. -/
theorem isStablePair_one (p : Profile 1) (m w : Fin 1) : IsStablePair p m w := by
  refine ⟨Equiv.refl _, ?_, Subsingleton.elim _ _⟩
  intro m' w' h
  exact h.1 (Subsingleton.elim _ _)

/-- A singleton agent has exactly one stable partner. -/
@[simp]
theorem manStablePartners_one (p : Profile 1) (m : Fin 1) :
    manStablePartners p m = Finset.univ := by
  ext w
  simp only [mem_manStablePartners, Finset.mem_univ, iff_true]
  exact isStablePair_one p m w

/-- A singleton agent on the other side also has exactly one stable partner. -/
@[simp]
theorem womanStablePartners_one (p : Profile 1) (w : Fin 1) :
    womanStablePartners p w = Finset.univ := by
  ext m
  simp only [mem_womanStablePartners, Finset.mem_univ, iff_true]
  exact isStablePair_one p m w

/-- A singleton market has one distinct stable pair. -/
@[simp]
theorem numStablePairs_one (p : Profile 1) : numStablePairs p = 1 := by
  simp [numStablePairs, isStablePair_one]

/-- Shuffling a singleton market leaves its one stable pair. -/
@[simp]
theorem expectedNumStablePairsAfterShuffle_one (p : Profile 1) :
    expectedNumStablePairsAfterShuffle p = 1 := by
  simp [expectedNumStablePairsAfterShuffle]

end StableMarriage
