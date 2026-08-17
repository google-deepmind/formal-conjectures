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
public import Mathlib.Combinatorics.SimpleGraph.Paths

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

/-- `G` is `k`-connected: it has more than `k` vertices, and it stays connected after the
removal of any set of fewer than `k` vertices.

Mathlib has `SimpleGraph.IsEdgeConnected`, but it has no vertex connectivity. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- A graph on at most `k` vertices is not `k`-connected. -/
theorem not_isKConnected_of_card_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : Fintype.card V ≤ k) : ¬ IsKConnected G k :=
  fun hG => absurd hG.1 (not_lt.mpr h)

end SimpleGraph
