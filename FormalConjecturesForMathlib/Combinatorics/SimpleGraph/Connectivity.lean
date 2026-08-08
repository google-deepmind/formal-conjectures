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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Nat.Lattice

@[expose] public section

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset List

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths. Note that graphs with at most one vertex are not classed as
infinitely connected.
-/
def InfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop := Nontrivial V ∧
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/-- The vertex connectivity `κ(G)`: the minimum number of vertices whose removal
disconnects the graph (or `n - 1` when the graph is complete).
Vertex connectivity is not yet in Mathlib; we define it here as the minimum size of
a vertex separator, where removing `S` leaves the induced subgraph on `Sᶜ` disconnected. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ :=
  if Fintype.card α ≤ 1 then 0
  else sInf { k | ∃ S : Finset α, S.card = k ∧
    (¬(G.induce (↑Sᶜ : Set α)).Connected ∨ S.card = Fintype.card α - 1) }

/-- The **edge connectivity** `λ(G)` of a simple graph `G`.

We define it as the minimum size of a set of edges `F ⊆ E(G)` whose removal
renders `G` disconnected.  If no such set exists (i.e., `G` has ≤ 1 vertex or
is already disconnected), we define `λ(G) = 0`. -/
noncomputable def edgeConnectivity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf { k | ∃ F : Finset (Sym2 α),
    F.card = k ∧
    (↑F : Set (Sym2 α)) ⊆ G.edgeSet ∧
    ¬ (G.deleteEdges ↑F).Connected }

end SimpleGraph
