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

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A cycle of `G`, carrying its basepoint. Bundling the basepoint makes the cycles of `G` into a
type, so they can be collected into a `Finset` or a `Multiset`. -/
structure Cycle (G : SimpleGraph V) where
  /-- The vertex the cycle starts and ends at. -/
  base : V
  /-- The closed walk tracing the cycle. -/
  walk : G.Walk base base
  /-- That walk is a cycle. -/
  isCycle : walk.IsCycle

/-- The edges a cycle traverses. -/
def Cycle.edges {G : SimpleGraph V} (c : Cycle G) : List (Sym2 V) := c.walk.edges

/-- The length of a cycle, its number of edges. -/
def Cycle.length {G : SimpleGraph V} (c : Cycle G) : ℕ := c.walk.length

/-- `G` is bridgeless if none of its edges is a bridge. -/
def IsBridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

/-- In a forest every edge is a bridge, so an acyclic bridgeless graph has no edges at all. -/
theorem edgeFinset_eq_empty_of_isBridgeless_of_isAcyclic [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hbr : G.IsBridgeless) : G.edgeFinset = ∅ := by
  rw [SimpleGraph.edgeFinset_eq_empty]
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hadj
  exact hbr s(u, v) hadj (G.isAcyclic_iff_forall_edge_isBridge.mp hacyc hadj)

end SimpleGraph
