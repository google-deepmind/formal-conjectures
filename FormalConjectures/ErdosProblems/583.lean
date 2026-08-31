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

import FormalConjecturesUtil

/-!
# Erdős Problem 583

*References:*
- [erdosproblems.com/583](https://www.erdosproblems.com/583)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open SimpleGraph

namespace Erdos583

/--
A subgraph `H` of `G` is a path subgraph if it is the subgraph traced out by a path in `G`,
i.e. a walk with no repeated vertices.
-/
def IsPathSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ H = p.toSubgraph

/--
`D` is a partition of `G` into edge-disjoint subgraphs: the edge sets of the members of `D`
are pairwise disjoint and their union is the edge set of `G`.
-/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

/--
Every connected graph on $n$ vertices can be partitioned into at most $\lceil n/2\rceil$
edge-disjoint paths.

A problem of Erdős and Gallai.
-/
@[category research open, AMS 5]
theorem erdos_583 {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧
      IsDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  sorry

end Erdos583
