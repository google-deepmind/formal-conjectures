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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Proper edge colourings and the chromatic index

Mathlib (as of 2026-08) has edge *labelings* but no chromatic index. This file defines proper
edge colourings `SimpleGraph.IsProperEdgeColoring`, the predicate `SimpleGraph.EdgeColorable`
and the **chromatic index** `SimpleGraph.chromaticIndex`, and proves the trivial bound
`χ'(G) ≤ |E(G)| + 1`.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Two edges are **adjacent** if they share a vertex. -/
def EdgesAdjacent (e f : Sym2 V) : Prop := ∃ v, v ∈ e ∧ v ∈ f

/-- A function `c` on edges is a **proper edge colouring** of `G` if distinct adjacent edges of
`G` receive different colours. -/
def IsProperEdgeColoring {α : Type*} (c : Sym2 V → α) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f → EdgesAdjacent e f → c e ≠ c f

/-- `G` is **`n`-edge-colourable** if it has a proper edge colouring with `n` colours. -/
def EdgeColorable (n : ℕ) : Prop :=
  ∃ c : Sym2 V → Fin n, G.IsProperEdgeColoring c

/-- The **chromatic index** `χ'(G)`: the least number of colours in a proper edge colouring. -/
noncomputable def chromaticIndex : ℕ :=
  sInf {n | G.EdgeColorable n}

/-- Any function injective on the edge set is a proper edge colouring. -/
theorem isProperEdgeColoring_of_injOn {α : Type*} {c : Sym2 V → α}
    (hc : Set.InjOn c G.edgeSet) : G.IsProperEdgeColoring c :=
  fun _ he _ hf hef _ h => hef (hc he hf h)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Colouring every edge with its own colour (and all non-edges with one spare colour):
`G` is `(|E(G)| + 1)`-edge-colourable. -/
theorem edgeColorable_card_edgeFinset_succ : G.EdgeColorable (G.edgeFinset.card + 1) := by
  classical
  refine ⟨fun e => if h : e ∈ G.edgeFinset then Fin.castSucc (G.edgeFinset.equivFin ⟨e, h⟩)
    else Fin.last _, G.isProperEdgeColoring_of_injOn ?_⟩
  intro e he f hf hef
  have he' : e ∈ G.edgeFinset := mem_edgeFinset.mpr he
  have hf' : f ∈ G.edgeFinset := mem_edgeFinset.mpr hf
  simp only [dif_pos he', dif_pos hf'] at hef
  have := G.edgeFinset.equivFin.injective (Fin.castSucc_injective _ hef)
  exact congrArg Subtype.val this

/-- The trivial bound `χ'(G) ≤ |E(G)| + 1`. -/
theorem chromaticIndex_le_card_edgeFinset_succ : G.chromaticIndex ≤ G.edgeFinset.card + 1 :=
  Nat.sInf_le G.edgeColorable_card_edgeFinset_succ

end SimpleGraph
