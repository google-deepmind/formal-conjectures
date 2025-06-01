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

/-- A Sidon sequence (also called a Sidon set) is a sequence of natural numbers $a_0, a_1, ...$
such that all pairwise sums $a_i + a_j$ are distinct for $i ≤ j$.

In other words, all pairwise sums of elements are distinct apart from coincidences forced by the
commutativity of addition. -/
def IsSidon {ι α : Type*} [Preorder ι] [Preorder α] [Add α] (a : ι →o α) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ ≤ j₁ → i₂ ≤ j₂ → a i₁ + a j₁ = a i₂ + a j₂ → i₁ = i₂ ∧ j₁ = j₂

lemma IsSidon.injective {ι α : Type*} [Preorder ι] [Preorder α] [Add α] (a : ι →o α) (ha : IsSidon a) :
    Injective a :=
  fun i₁ i₂ hi ↦ (ha i₁ i₁ i₂ i₂ (le_refl _) (le_refl _) (by rw [hi])).1

variable {α : Type*} [AddCommMonoid α]

/-- The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite). -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, d ≠ 0 ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

lemma Set.IsAPOfLength.card (s : Set α) (l : ℕ∞) (hs : s.IsAPOfLength l) :
    ENat.card s = l := by
  sorry

lemma IsSidon.avoids_isAPOfLength_three {α : Type*} [OrderedAddCommMonoid α]
    (A : ℕ →o α) (hA : IsSidon A) :
    (∀ Y, IsAPOfLength Y 3 → ((range A) ∩ Y).ncard ≤ 2) := by
  sorry
