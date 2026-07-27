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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `largestInducedForestSize G` is the size of a largest induced forest of `G`. -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

omit [Fintype α] in
/-- An induced subgraph is bipartite exactly when its vertices admit a two-coloring. -/
theorem induce_isBipartite_iff_exists_coloring (G : SimpleGraph α) (s : Finset α) :
    (G.induce s).IsBipartite ↔
      ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨c⟩
    refine ⟨fun v => if hv : v ∈ s then c ⟨v, hv⟩ else 0, ?_⟩
    intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    exact c.valid huv
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk (fun v => c v) fun {u v} huv => hc u u.prop v v.prop huv⟩

/-- Computable largest induced bipartite subgraph size via powerset enumeration. -/
def computableLargestInducedBipartiteSubgraphSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter fun s : Finset α =>
    ∃ c : α → Fin 2, ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v).sup Finset.card

/-- The computable largest induced bipartite subgraph size agrees with the `sSup` definition. -/
theorem largestInducedBipartiteSubgraphSize_eq_computable
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.largestInducedBipartiteSubgraphSize = G.computableLargestInducedBipartiteSubgraphSize := by
  unfold largestInducedBipartiteSubgraphSize computableLargestInducedBipartiteSubgraphSize
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨s, hs, rfl⟩
      apply Finset.le_sup
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ s),
        (induce_isBipartite_iff_exists_coloring G s).mp hs⟩
  · apply Finset.sup_le
    intro s hs
    apply le_csSup
    · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨s, (induce_isBipartite_iff_exists_coloring G s).mpr
        (Finset.mem_filter.mp hs).2, rfl⟩

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`.
Returned as a real number. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

end SimpleGraph
