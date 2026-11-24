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

public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of one-dimensional representations

This file proves that every one-dimensional representation of a monoid on a field is irreducible.
-/

@[expose] public section

/-- Every one-dimensional representation of $G$ on a field $k$ is irreducible. -/
theorem isIrreducible_one_dim {k G : Type*} [Field k] [Monoid G] (ρ : Representation k G k) :
    ρ.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 : (1 : k) ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    change (1 : k) ∈ (⊥ : Submodule k k) at h1
    simp at h1
  · rcases eq_bot_or_eq_top W.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
