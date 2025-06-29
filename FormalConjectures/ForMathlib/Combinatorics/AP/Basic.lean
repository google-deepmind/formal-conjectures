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
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

variable {α : Type*} [AddCommMonoid α]

def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  d ≠ 0 ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

theorem Set.IsAPOfLengthWith.zero (s : Set α) (a d : α) :
    s.IsAPOfLengthWith 0 a d ↔ d ≠ 0 ∧ s = ∅ := by
  simp [Set.IsAPOfLengthWith]

theorem Set.IsAPOfLengthWith.one (s : Set α) (a d : α) :
    s.IsAPOfLengthWith 1 a d ↔ d ≠ 0 ∧ s = {a} := by
  simp [Set.IsAPOfLengthWith, zero_nsmul]

theorem Set.isAPOfLengthWith_pair {α : Type*} [AddCommGroup α] {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  simp [Set.IsAPOfLengthWith, sub_ne_zero_of_ne hab.symm]
  refine Set.ext fun x => ⟨fun h ↦ ?_, fun ⟨n, ⟨_, _⟩⟩ ↦ by interval_cases n <;> simp_all [zero_nsmul]⟩
  cases h with
  | inl hl => use 0; simp [zero_nsmul, hl]
  | inr hr => exact ⟨1, by norm_num, by simp_all [hr, add_assoc]⟩

theorem Nat.isAPOfLengthWith_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hab
  simp [Set.IsAPOfLengthWith, Nat.sub_ne_zero_of_lt hab, h, add_assoc, Nat.add_sub_cancel_left]
  refine Set.ext fun x => ⟨fun a => ?_, fun ⟨w, ⟨hl, hr⟩⟩ => by interval_cases w <;> simp_all [add_assoc]⟩
  cases a with
  | inl _ => simp_all
  | inr hr => exact ⟨1, by norm_num, by simp_all [hr, add_assoc]⟩

/-- The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite). -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- Only the empty set is a finite arithmetic progression of length $0$. -/
theorem Set.IsAPOfLength.zero {α : Type*} [AddCommMonoidWithOne α] [NeZero (1 : α)] {s : Set α} :
    s.IsAPOfLength 0 ↔ s = ∅ := by
  simp [Set.IsAPOfLength, Set.IsAPOfLengthWith.zero]
  rintro rfl
  exact ⟨1, by simp⟩

/-- Only singletons are finite arithmetic progressions of length $1$. -/
theorem Set.IsAPOfLength.one {α : Type*} [AddCommMonoidWithOne α] [NeZero (1 : α)] {s : Set α} :
    s.IsAPOfLength 1 ↔ ∃ a₀, s = {a₀} := by
  simp [IsAPOfLength, zero_nsmul, IsAPOfLengthWith.one]
  intro _ _
  exact ⟨1, by simp⟩

theorem Set.isAPOfLength_singleton {α : Type*} [AddCommMonoidWithOne α] [NeZero (1 : α)] (a : α) :
    Set.IsAPOfLength {a} 1 := by
  simp [IsAPOfLength.one]

theorem Set.isAPOfLength_pair {α : Type*} [AddCommGroup α] {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLength {a, b} 2 := by
  simpa [IsAPOfLength] using ⟨a, b - a, Set.isAPOfLengthWith_pair hab⟩

theorem Nat.isAPOfLength_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLength {a, b} 2 := by
  simpa [Set.IsAPOfLength] using ⟨a, b - a, Nat.isAPOfLengthWith_pair hab⟩

def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → t.ncard = 1

/-- Every set contains an arithmetic progression of length zero. -/
@[simp]
theorem Set.not_isAPOfLengthFree_zero {α : Type*} [AddCommMonoidWithOne α] [NeZero (1 : α)]
    (s : Set α) : ¬s.IsAPOfLengthFree 0 := by
  simpa [Set.IsAPOfLengthFree, Set.IsAPOfLength.zero] using fun x ↦ by simp [Ne.symm]

lemma Set.IsAPOfLength.card [IsLeftCancelAdd α] (s : Set α) (l : ℕ∞) (hs : s.IsAPOfLength l) :
    ENat.card s = l := by
  sorry

theorem Set.IsAPOfLength.injective [IsLeftCancelAdd α] {s : Set α} {l₁ l₂ : ℕ∞} (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.card, h₂.card]

theorem Set.not_isAPOfLength_empty {α : Type*} [AddCommMonoidWithOne α] [NeZero (1 : α)]
    [IsLeftCancelAdd α] {l : ℕ∞} (hl : 0 < l) :
    ¬Set.IsAPOfLength (∅ : Set α) l :=
  fun h ↦ by simp_all [h.injective <| Set.IsAPOfLength.zero.2 rfl]
