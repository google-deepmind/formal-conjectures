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

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder

open Function Set

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite). -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, d ≠ 0 ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

lemma Set.IsAPOfLength.card (s : Set α) (l : ℕ∞) (hs : s.IsAPOfLength l) :
    ENat.card s = l := by
  sorry

lemma IsSidon.avoids_isAPOfLength_three {α : Type*} [AddCommMonoid α] (A : Set ℕ) (hA : IsSidon A) :
    (∀ Y, IsAPOfLength Y 3 → (A ∩ Y).ncard ≤ 2) := by
  sorry
