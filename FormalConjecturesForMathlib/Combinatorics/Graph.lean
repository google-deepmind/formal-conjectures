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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Flows on multigraphs

This file defines walks, connectivity, bridges, orientations, networks, and flows for `Graph`.
-/

@[expose] public section

namespace Graph

universe u v

variable {α : Type u} {β : Type v} {M : Type*} {G : Graph α β}

/-- A finite walk in a graph. -/
inductive Walk (G : Graph α β) : α → α → Type max u v
  | nil {u : α} : G.Walk u u
  | cons {u v w : α} {e : β} (h : G.IsLink e u v) (p : G.Walk v w) : G.Walk u w
  deriving DecidableEq

/-- Two vertices are reachable if there is a walk between them. -/
def Reachable (G : Graph α β) (u v : α) : Prop := Nonempty (G.Walk u v)

/-- A graph is connected if every pair of its vertices is reachable. -/
def Connected (G : Graph α β) : Prop :=
  ∀ v ∈ G.vertexSet, ∀ w ∈ G.vertexSet, G.Reachable v w

/-- An edge is a bridge if deleting it makes its endpoints unreachable from each other. -/
def IsBridge (G : Graph α β) (e : β) : Prop :=
  ∃ a b : α, G.IsLink e a b ∧ ¬ (G.deleteEdges {e}).Reachable a b

/-- Capacity bounds and vertex balances for a flow on a graph. -/
structure Network (G : Graph α β) (M : Type*) [AddCommGroup M] [Preorder M] where
  strictSet : Set α := G.vertexSet
  strictSet_subset_vertexSet : strictSet ⊆ G.vertexSet := by simp
  balance (v : α) : M
  low (e : β) : M
  up (e : β) : M

/-- A choice of direction for every edge of a graph. -/
structure Orientation (G : Graph α β) where
  source : G.edgeSet → α
  target : G.edgeSet → α
  isLink (e : G.edgeSet) : G.IsLink e.1 (source e) (target e)

/-- A flow obeys the capacity bounds and has the prescribed net balance at every vertex. -/
noncomputable def IsFlow [DecidableEq α] [Fintype G.edgeSet] [AddCommGroup M] [Preorder M]
    (O : Orientation G) (N : Network G M) (f : β → M) : Prop :=
  (∀ e : β, e ∈ G.edgeSet → N.low e ≤ f e) ∧
  (∀ e : β, e ∈ G.edgeSet → f e ≤ N.up e) ∧
  ∀ v : α, v ∈ G.vertexSet →
    (∑ e : G.edgeSet, if O.source e = v then f e.1 else 0) -
      (∑ e : G.edgeSet, if O.target e = v then f e.1 else 0) = N.balance v

/-- The zero-balance network whose edge flows have absolute value strictly less than `k`. -/
def zeroKNetwork (G : Graph α β) (k : ℕ) : Network G ℤ where
  balance _ := 0
  low _ := -(k : ℤ) + 1
  up _ := (k : ℤ) - 1

end Graph
