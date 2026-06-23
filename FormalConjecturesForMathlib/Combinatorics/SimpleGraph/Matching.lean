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

end SimpleGraph
