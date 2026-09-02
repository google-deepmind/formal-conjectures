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

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- `G` is a **unique subgraph** of `H` if there is exactly one subgraph of `H` isomorphic to
`G`. Subgraphs of `H` are taken in the spanning sense: elements `G' ≤ H` of the lattice
`SimpleGraph V`, i.e. subsets of the edges of `H` (not necessarily induced). -/
def IsUniqueSubgraph (G H : SimpleGraph V) : Prop :=
  ∃! G' : SimpleGraph V, G' ≤ H ∧ Nonempty (G.Iso G')

/-- The number of distinct unique subgraphs of `H`: the number of isomorphism classes of graphs
that occur exactly once as a subgraph of `H`. Each such class contains exactly one subgraph
`G ≤ H` (uniqueness forbids a second isomorphic copy), so counting those representatives counts
the classes. -/
noncomputable def uniqueSubgraphCount (H : SimpleGraph V) : ℕ :=
  {G : SimpleGraph V | G ≤ H ∧ IsUniqueSubgraph G H}.ncard

end SimpleGraph
