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

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Lattice.Nat

/-!
# Subgraph criticality and bipartization
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/--
A graph `G` is `k`-critical if it has chromatic number `k` and every proper subgraph has
chromatic number `< k`.
-/
def IsSubgraphCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < k

/-- The least number of edges whose deletion makes `G` bipartite. -/
noncomputable def bipartizationNumber [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ E ⊆ G.edgeSet, E.ncard = m ∧ (G.deleteEdges E).IsBipartite}

end SimpleGraph
