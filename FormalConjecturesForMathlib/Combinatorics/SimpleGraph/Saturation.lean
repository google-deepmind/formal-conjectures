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

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

/-!
The saturation number of a graph.

Main definitions

* `SimpleGraph.saturationNumber`   : the saturation number `μ*(G)`, the minimum
  size of a maximal matching.
* `SimpleGraph.computable_sat_num` : a computable companion definition.
* `SimpleGraph.sat_num_eq_computable` : bridge equation
  `saturationNumber G = computable_sat_num G`.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

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
