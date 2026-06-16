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
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

/-!
Maximal matchings and the saturation number

This file introduces maximal matchings (described as finite sets of edges) and
the saturation number of a graph.

Main definitions

* `SimpleGraph.IsEdgeMatching`        : a finite set of edges forming a matching.
* `SimpleGraph.IsMaximalEdgeMatching` : a matching to which no edge can be added.
* `SimpleGraph.saturationNumber`      : the saturation number `μ*(G)`, the
  minimum size of a maximal matching.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Matchings as edge sets -/

/-- A finite set of edges `M` is a *matching* of `G` if every element of `M` is
an edge of `G` and any two edges of `M` are equal or share no vertex (no vertex
is covered twice). -/
def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

instance (G : SimpleGraph α) [DecidableRel G.Adj] (M : Finset (Sym2 α)) :
    Decidable (G.IsEdgeMatching M) := by
  unfold IsEdgeMatching; infer_instance

/-- A matching `M` of `G` is *maximal* if no further edge of `G` can be added to
`M` while keeping the matching property. -/
def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  G.IsEdgeMatching M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ G.IsEdgeMatching (insert e M)

instance (G : SimpleGraph α) [DecidableRel G.Adj] (M : Finset (Sym2 α)) :
    Decidable (G.IsMaximalEdgeMatching M) := by
  unfold IsMaximalEdgeMatching; infer_instance

/-! ### Saturation number -/

/-- The *saturation number* `μ*(G)` (also called the lower matching number): the
minimum number of edges in a maximal matching of `G`.

Every finite graph has a maximal matching (extend the empty matching greedily),
so this set is nonempty and the infimum is a genuine minimum. -/
noncomputable def saturationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsMaximalEdgeMatching M ∧ M.card = n}

/-- Computable saturation number via powerset enumeration over the edge set. -/
def computable_sat_num (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ((G.edgeFinset.powerset.filter fun M => G.IsMaximalEdgeMatching M).image
    Finset.card).min.getD 0

/-! ### Saturation number equivalence -/

theorem sat_num_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    saturationNumber G = computable_sat_num G := by
  unfold saturationNumber computable_sat_num
  have hset : {n | ∃ M : Finset (Sym2 α), G.IsMaximalEdgeMatching M ∧ M.card = n}
      = ↑((G.edgeFinset.powerset.filter fun M => G.IsMaximalEdgeMatching M).image
          Finset.card) := by
    ext n
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_powerset, Set.mem_setOf_eq]
    refine ⟨fun ⟨M, hM, hn⟩ =>
        ⟨M, ⟨fun e he => mem_edgeFinset.mpr (hM.1.1 e he), hM⟩, hn⟩,
      fun ⟨M, ⟨_, hM⟩, hn⟩ => ⟨M, hM, hn⟩⟩
  rw [hset]
  set s : Finset ℕ :=
    (G.edgeFinset.powerset.filter fun M => G.IsMaximalEdgeMatching M).image Finset.card
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, Finset.coe_empty, Nat.sInf_empty, Finset.min_empty]; rfl
  · rw [hs.csInf_eq_min', ← Finset.coe_min' hs]; rfl

end SimpleGraph
