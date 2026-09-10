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

public import Mathlib.Topology.KrullDimension

/-!
# The dimension drop for proper closed subsets

A chain of irreducible closed subsets of a proper closed subspace can be extended by the
whole irreducible ambient space. Consequently a finite dimension bound drops strictly on a
proper closed subspace. This is a Krull-dimension statement, not a statement about the
singular or sheaf homology of an analytic space.
-/

@[expose] public section

open Topology TopologicalSpace Order

variable {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]

/-- A proper closed subspace of an irreducible space has dimension strictly below any
finite upper bound for the ambient dimension. Empty subspaces have dimension `⊥`, so this
also includes the dimension-zero case. -/
theorem topologicalKrullDim_lt_of_isClosed_of_ne_univ {S : Set X}
    (hS : IsClosed S) (hproper : S ≠ Set.univ) {n : ℕ}
    (hdim : topologicalKrullDim X ≤ n) : topologicalKrullDim S < n := by
  apply krullDim_lt_coe_iff.mpr
  intro l
  let φ := IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
  have hφ : StrictMono φ :=
    IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let topX : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlast : (l.map φ hφ).last < topX := by
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro he
    have hsub : (φ l.last : Set X) ⊆ S :=
      closure_minimal (by rintro _ ⟨x, _, rfl⟩; exact x.2) hS
    have he' : φ l.last = topX := he
    rw [he'] at hsub
    exact hproper (Set.Subset.antisymm (Set.subset_univ S) hsub)
  have hle := (LTSeries.length_le_krullDim ((l.map φ hφ).snoc topX hlast)).trans hdim
  have hnat : l.length + 1 ≤ n := by exact_mod_cast hle
  omega
