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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The set of edge distances to a bipartite graph is always non-empty because deleting all edges
from a graph makes it bipartite.
-/
@[category test, AMS 5]
theorem SimpleGraph.edgeDistancesToBipartite_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    SimpleGraph.edgeDistancesToBipartite A |>.Nonempty := by
  dsimp only [edgeDistancesToBipartite,Set.nonempty_def]
  refine ⟨_, Set.univ, ?_, rfl⟩
  use fun v => 0
  simp

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
The set of minimum edge distances to bipartite for subgraphs of size `n` is bounded above.
A graph on `n` vertices has at most `n choose 2` edges, and deleting all of them
makes the graph bipartite, providing a straightforward upper bound.
-/
@[category test, AMS 5]
theorem SimpleGraph.subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  use n.choose 2
  simp only [upperBounds, Set.mem_setOf_eq, SimpleGraph.subgraphEdgeDistsToBipartite,
    SimpleGraph.minEdgeDistToBipartite, SimpleGraph.edgeDistancesToBipartite]
  intro m h
  replace ⟨A, ⟨hn, h_fin, h⟩⟩ := h
  rw [← h]
  have : A.edgeSet.ncard ≤ n.choose 2 := by
    rw [← hn]
    have := h_fin.fintype
    have := Fintype.ofFinite ↑A.coe.edgeSet
    convert (A.coe).card_edgeFinset_le_card_choose_two
    · rw [← Set.ncard_coe_Finset A.coe.edgeFinset, coe_edgeFinset A.coe, ← Subgraph.image_coe_edgeSet_coe A]
      exact (Set.ncard_image_iff (Set.toFinite A.coe.edgeSet)).mpr <|
        Function.Injective.injOn <| Sym2.map.injective Subtype.coe_injective
    · rw [Set.ncard_eq_toFinset_card _ h_fin, Set.Finite.card_toFinset]
  refine le_trans ?_ this
  apply Nat.sInf_le
  simp only [Subgraph.deleteEdges_verts, exists_prop, Set.mem_setOf_eq]
  use A.edgeSet
  constructor
  · use 0
    rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨_, hvw⟩
    aesop
  · rfl

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74 : (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ G : SimpleGraph V, G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)) ↔ answer(sorry):= by
  sorry

/--
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $\sqrt{n}$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74.variants.sqrt : (∃ G : SimpleGraph V, G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ (n : ℝ).sqrt) ↔ answer(sorry):= by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74
