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

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Lattice.Nat

/-!
# Colour-avoidance Ramsey numbers

The colour-avoidance Ramsey number is the least size of a complete graph in which every
edge colouring has a prescribed-size vertex set avoiding a monochromatic clique in some colour.

*Reference:* [Erdős problem 129](https://www.erdosproblems.com/129)
-/

@[expose] public section

namespace Combinatorics.ColorAvoidance

/-- Every edge between distinct vertices of `T` has colour `i` under `c`.
Values of `c` on diagonal pairs are ignored. -/
def IsMonoClique {V α : Type*} (c : Sym2 V → α) (i : α) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c s(x, y) = i

/-- Every subset of a monochromatic clique is monochromatic in the same colour. -/
theorem IsMonoClique.mono {V α : Type*} {c : Sym2 V → α} {i : α}
    {S T : Finset V} (hT : IsMonoClique c i T) (hST : S ⊆ T) : IsMonoClique c i S := by
  intro x hx y hy hxy
  exact hT x (hST hx) y (hST hy) hxy

/-- The empty vertex set is monochromatic in every colour. -/
@[simp] theorem isMonoClique_empty {V α : Type*} (c : Sym2 V → α) (i : α) :
    IsMonoClique c i ∅ := by
  simp [IsMonoClique]

/-- Every singleton is monochromatic in every colour. -/
@[simp] theorem isMonoClique_singleton {V α : Type*} (c : Sym2 V → α) (i : α) (v : V) :
    IsMonoClique c i {v} := by
  simp [IsMonoClique]

/-- Every `r`-colouring of the edges of the complete graph on `N` vertices has an `n`-vertex
set containing no monochromatic `k`-clique in at least one colour. -/
def HasRamseyProperty (n k r N : ℕ) : Prop :=
  ∀ c : Sym2 (Fin N) → Fin r, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ i : Fin r, ∀ T ⊆ S, T.card = k → ¬ IsMonoClique c i T

/-- The least `N` with the colour-avoidance Ramsey property for `(n, k, r)`.
This is `0` if no such `N` exists. -/
noncomputable def ramseyNumber (n k r : ℕ) : ℕ := sInf {N | HasRamseyProperty n k r N}

/-- Any witness to the Ramsey property bounds the colour-avoidance Ramsey number. -/
theorem ramseyNumber_le {n k r N : ℕ} (h : HasRamseyProperty n k r N) :
    ramseyNumber n k r ≤ N := Nat.sInf_le h

/-- When a witness exists, the colour-avoidance Ramsey number has the Ramsey property. -/
theorem hasRamseyProperty_ramseyNumber {n k r : ℕ}
    (h : ∃ N, HasRamseyProperty n k r N) : HasRamseyProperty n k r (ramseyNumber n k r) :=
  Nat.sInf_mem h

end Combinatorics.ColorAvoidance
