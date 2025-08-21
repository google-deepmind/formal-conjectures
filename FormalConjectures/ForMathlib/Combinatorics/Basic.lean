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

import FormalConjectures.ForMathlib.Combinatorics.AP.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice

open Function Set

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set such that all pairwise sums of elements are distinct,
apart from coincidences forced by commutativity. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

lemma IsSidon.avoids_isAPOfLength_three {α : Type*} [AddCommMonoid α] (A : Set ℕ) (hA : IsSidon A) :
    (∀ Y, IsAPOfLength Y 3 → (A ∩ Y).ncard ≤ 2) := by
  sorry

noncomputable instance IsSidon.decide [AddCommMonoid α] (s : Set α): Decidable (IsSidon s) := by
  exact Classical.propDecidable _

/-- The subsets of `{0, ..., n - 1}` which are Sidon sets. -/
noncomputable def SidonSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter fun s => IsSidon (s : Set ℕ)

/-- The sizes of Sidon subsets of `{0, ..., n - 1}`. -/
noncomputable def SidonSubsetsSizes (n : ℕ) : Finset ℕ :=
  (SidonSubsets n).image Finset.card

lemma SidonSubsetsSizesNonempty (n : ℕ) : (SidonSubsetsSizes n).Nonempty := by
  use 0
  simp only [SidonSubsetsSizes, Finset.mem_image]
  use ∅
  simp [SidonSubsets, IsSidon, Set.Pairwise, Finset.mem_filter, Finset.mem_powerset, Finset.card_empty]

/-- The maximum size of a Sidon set in `{1, ..., N}`. -/
noncomputable def maxSidonSetSize (N : ℕ) : ℕ :=
  sSup {(A.card) | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N) (_ : IsSidon A.toSet)}

