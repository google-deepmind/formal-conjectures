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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice

/-!
# Hypergraph Ramsey Numbers

This file defines the `r`-uniform hypergraph Ramsey number `R_r(n)`.
-/

namespace Combinatorics

/--
The `r`-uniform hypergraph Ramsey number `R_r(n)`.
The smallest natural number `m` such that every 2-coloring of the `r`-subsets of a set of size `m`
contains a monochromatic subset of size `n`.
-/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf { m | ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)), S.card = n ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }

/-- `n ≤ hypergraphRamsey r n` when the set is nonempty. -/
theorem le_hypergraphRamsey (r n : ℕ) (hne : { m | ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)), S.card = n ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }.Nonempty) :
    n ≤ hypergraphRamsey r n := by
  apply le_csInf hne
  intro m hm
  have : ∃ (S : Finset (Fin m)), S.card = n ∧ _ := hm (fun _ ↦ false)
  obtain ⟨S, hS, -⟩ := this
  calc n = S.card := hS.symm
    _ ≤ Fintype.card (Fin m) := Finset.card_le_univ S
    _ = m := Fintype.card_fin m

/-- `hypergraphRamsey r r = r` for any `r`. -/
theorem hypergraphRamsey_self (r : ℕ) : hypergraphRamsey r r = r := by
  have h_mem : r ∈ { m | ∀ (c : Finset (Fin m) → Bool),
      ∃ (S : Finset (Fin m)), S.card = m ∧
        ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color } := by
    intro c
    refine ⟨Finset.univ, ?_, c Finset.univ, ?_⟩
    · simp [Fintype.card_fin]
    · intro e _ he_card
      congr 1
      exact Finset.eq_univ_of_card e (he_card.trans (Fintype.card_fin r).symm)
  exact le_antisymm (Nat.sInf_le h_mem) (le_hypergraphRamsey r r ⟨r, h_mem⟩)

end Combinatorics
