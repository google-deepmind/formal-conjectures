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

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Finite covers by translates

Translation centers may lie anywhere in the ambient additive group. The covering
number is the infimum of finite cover sizes; use `Coverable` when a cover is required.

Definitions adapted from OpenAI's
[MetricEntropyDuality](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MetricEntropyDuality.lean),
Apache-2.0. The ambient type was generalized and names were changed.
-/

@[expose] public section

namespace TranslativeCover

variable {E : Type*} [AddGroup E]

/-- A finite list of centers whose translates of `B` cover `A`. -/
def Covers {m : ℕ} (A B : Set E) (centers : Fin m → E) : Prop :=
  ∀ x ∈ A, ∃ j, x - centers j ∈ B

/-- Existence of a finite cover by translates. -/
def Coverable (A B : Set E) : Prop := ∃ m, ∃ centers : Fin m → E, Covers A B centers

/-- The least finite cover size when `Coverable A B` holds. -/
noncomputable def coveringNumber (A B : Set E) : ℕ :=
  sInf {m : ℕ | ∃ centers : Fin m → E, Covers A B centers}

theorem exists_cover_min {A B : Set E} (h : Coverable A B) :
    ∃ centers : Fin (coveringNumber A B) → E, Covers A B centers :=
  Nat.sInf_mem h

theorem covers_zero_iff (A B : Set E) (centers : Fin 0 → E) :
    Covers A B centers ↔ A = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j, _⟩ := h x hx
    exact Fin.elim0 j
  · rintro rfl x hx
    exact hx.elim

end TranslativeCover
