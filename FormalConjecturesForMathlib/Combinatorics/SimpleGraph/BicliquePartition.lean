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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Partitions into complete bipartite subgraphs
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A complete bipartite subgraph of `G`, given by its two disjoint parts. -/
structure Biclique (G : SimpleGraph V) where
  /-- One part of the biclique. -/
  left : Finset V
  /-- The other part of the biclique. -/
  right : Finset V
  disjoint : Disjoint left right
  complete : ∀ u ∈ left, ∀ v ∈ right, G.Adj u v

/-- The edges of a biclique. -/
def Biclique.edgeSet {G : SimpleGraph V} (B : Biclique G) : Set (Sym2 V) :=
  {e | ∃ u ∈ B.left, ∃ v ∈ B.right, e = s(u, v)}

/-- The bipartition number $\tau(G)$ of a graph $G$: the smallest number of pairwise edge
disjoint complete bipartite subgraphs whose union is $G$. -/
noncomputable def bipartitionNumber [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ B : Fin k → Biclique G,
    (Pairwise fun i j ↦ Disjoint (B i).edgeSet (B j).edgeSet) ∧ ⋃ i, (B i).edgeSet = G.edgeSet}

end SimpleGraph
