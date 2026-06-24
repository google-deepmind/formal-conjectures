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
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Real.Archimedean

@[expose] public section

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical Finset List

/-- `matchingNumber G` is the size of a maximum matching of `G`. -/
noncomputable def matchingNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => (M.edgeSet.toFinset.card : ℝ)) matchings)


/-- In a finite graph, twice the number of edges of any matching is at most the number of
vertices: each edge contributes two distinct vertices, and a matching's edges are vertex-disjoint. -/
theorem matching_card_bound (G : SimpleGraph α) (M : Subgraph G) [Fintype ↥M.edgeSet]
    (h : M.IsMatching) : 2 * M.edgeSet.toFinset.card ≤ Fintype.card α := by
  have hdisj : ∀ e ∈ M.edgeSet.toFinset, ∀ f ∈ M.edgeSet.toFinset, e ≠ f →
      Disjoint e.toFinset f.toFinset := by
    intro e he f hf hef
    rw [Set.mem_toFinset] at he hf
    rw [Finset.disjoint_left]; intro x hxe hxf
    rw [Sym2.mem_toFinset] at hxe hxf
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf
    rw [Subgraph.mem_edgeSet] at he hf
    apply hef; rw [h.eq_of_adj_left he hf]
  have hcard2 : ∀ e ∈ M.edgeSet.toFinset, e.toFinset.card = 2 := by
    intro e he; rw [Set.mem_toFinset] at he
    exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset he))
  calc 2 * M.edgeSet.toFinset.card
      = ∑ e ∈ M.edgeSet.toFinset, e.toFinset.card := by
        rw [Finset.sum_congr rfl hcard2, Finset.sum_const, smul_eq_mul]; omega
    _ = (M.edgeSet.toFinset.biUnion Sym2.toFinset).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card α := by rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)

end SimpleGraph
