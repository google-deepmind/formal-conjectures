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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.ClosedSubsetDimensionDrop
public import Mathlib.Topology.NoetherianSpace

/-!
# Dimension drops on closed nowhere-dense subsets of Noetherian spaces

The ambient space need not be irreducible. Every irreducible chain on the closed subset
can be extended by an actual ambient irreducible component. Noetherianity gives that
component a nonempty open subset, so density of the complement ensures that the extension
is strict. This supplies the dimension drop at every reduced singular-remainder step,
including reducible remainders.
-/

@[expose] public section

open Topology TopologicalSpace Order

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- A closed subset with dense complement has strictly smaller finite Krull dimension,
even when the ambient space is reducible. -/
theorem topologicalKrullDim_lt_of_isClosed_of_dense_compl {S : Set X}
    (hS : IsClosed S) (hdense : Dense Sᶜ) {n : ℕ}
    (hdim : topologicalKrullDim X ≤ n) : topologicalKrullDim S < n := by
  apply krullDim_lt_coe_iff.mpr
  intro l
  let φ := IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
  have hφ : StrictMono φ :=
    IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  obtain ⟨Z, hZ, hsubZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (φ l.last : Set X) (φ l.last).isIrreducible
  let Z' : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hlast : (l.map φ hφ).last < Z' := by
    refine lt_of_le_of_ne hsubZ ?_
    intro he
    have hsub : (φ l.last : Set X) ⊆ S :=
      closure_minimal (by rintro _ ⟨x, _, rfl⟩; exact x.2) hS
    have he' : φ l.last = Z' := he
    rw [he'] at hsub
    obtain ⟨U, hU, hUne, hUZ⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
    obtain ⟨x, hxU, hxnot⟩ := hdense.inter_open_nonempty U hU hUne
    exact hxnot (hsub (hUZ hxU))
  have hle := (LTSeries.length_le_krullDim ((l.map φ hφ).snoc Z' hlast)).trans hdim
  exact_mod_cast hle
