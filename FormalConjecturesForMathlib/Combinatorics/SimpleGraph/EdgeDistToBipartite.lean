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

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Set.Card

/-!
# Edge distance to bipartite

For a graph `G` and `n : ℕ`, `G.maxSubgraphEdgeDistToBipartite n` is the least `k` such that
every subgraph of `G` on `n` vertices can be made bipartite by deleting at most `k` edges.
This is the function $h_G(n)$ of Definition 3.1 in [EHS82], used in Erdős Problems 74 and 111.

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/

@[expose] public section

namespace SimpleGraph

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

set_option backward.isDefEq.respectTransparency false in
/--
The set of edge distances to a bipartite graph is always non-empty because deleting all edges
from a graph makes it bipartite.
-/
theorem edgeDistancesToBipartite_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    edgeDistancesToBipartite A |>.Nonempty := by
  dsimp only [edgeDistancesToBipartite,Set.nonempty_def]
  refine ⟨_, A.edgeSet, fun _ a ↦ a, ?_, rfl⟩
  use fun _ => 0
  simp

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
finite subgraphs `A` of `G` on `n` vertices.
-/
def subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

set_option backward.isDefEq.respectTransparency false in
/--
The set of minimum edge distances to bipartite for subgraphs of size `n` is bounded above.
A graph on `n` vertices has at most `n choose 2` edges, and deleting all of them
makes the graph bipartite, providing a straightforward upper bound.
-/
theorem subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (subgraphEdgeDistsToBipartite G n) := by
  use n.choose 2
  simp only [upperBounds, Set.mem_ofPred_eq, SimpleGraph.subgraphEdgeDistsToBipartite,
    SimpleGraph.minEdgeDistToBipartite, SimpleGraph.edgeDistancesToBipartite]
  intro m h
  replace ⟨A, ⟨hn, h_fin, h⟩⟩ := h
  rw [← h]
  have : A.edgeSet.ncard ≤ n.choose 2 := by
    rw [← hn]
    have := h_fin.fintype
    have := Fintype.ofFinite ↑A.coe.edgeSet
    convert (A.coe).card_edgeFinset_le_card_choose_two
    · rw [← Set.ncard_coe_finset A.coe.edgeFinset, coe_edgeFinset A.coe,
        ← Subgraph.image_coe_edgeSet_coe A]
      exact (Set.ncard_image_iff (Set.toFinite A.coe.edgeSet)).mpr <|
        Function.Injective.injOn <| Sym2.map.injective Subtype.coe_injective
    · rw [Set.ncard_eq_toFinset_card _ h_fin, Set.Finite.card_toFinset]
  refine le_trans ?_ this
  apply Nat.sInf_le
  simp only [Subgraph.deleteEdges_verts, exists_prop, Set.mem_ofPred_eq]
  use A.edgeSet
  refine ⟨by rfl, ?_, rfl⟩
  use fun _ => 0
  simp

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges. This is the function $h_G(n)$ of Definition 3.1 in [EHS82].

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs (see `subgraphEdgeDistsToBipartite_bddAbove`). It is `0` if `G`
has fewer than `n` vertices.
-/
noncomputable def maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| subgraphEdgeDistsToBipartite G n

end SimpleGraph
