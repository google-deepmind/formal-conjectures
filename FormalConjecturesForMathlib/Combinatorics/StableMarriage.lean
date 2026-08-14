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

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-!
# Stable marriage

A minimal finite model of the stable marriage problem with complete strict preferences.
-/

namespace StableMarriage

/-- A preference profile for `n` men and `n` women. Each permutation maps a candidate to their
rank, with lower ranks preferred. -/
structure Profile (n : ℕ) where
  /-- The rank that each man assigns to each woman. -/
  manRank : Fin n → Equiv.Perm (Fin n)
  /-- The rank that each woman assigns to each man. -/
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving Inhabited

/-- Preference profiles form a finite type. -/
instance {n : ℕ} : Fintype (Profile n) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.manRank, p.womanRank)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A complete matching of `n` men to `n` women. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A man and woman form a blocking pair when they are not matched to each other and each ranks
the other above their current partner. -/
def IsBlockingPair {n : ℕ} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
    p.manRank m w < p.manRank m (μ m) ∧
      p.womanRank w m < p.womanRank w (μ.symm w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n : ℕ} (p : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair p μ m w

/-- The number of stable complete matchings for a preference profile. -/
noncomputable def numStableMatchings {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n // IsStable p μ}

end StableMarriage
