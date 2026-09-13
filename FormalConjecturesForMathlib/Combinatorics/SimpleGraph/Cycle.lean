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
public import Mathlib.Data.Set.Card

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

/-- The chords (also called diagonals) of a cycle: edges of `G` that join two vertices of
the cycle and are not themselves edges of the cycle. -/
def Cycle.chords {G : SimpleGraph V} (c : Cycle G) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ c.walk.support) ∧ e ∉ c.edges}

lemma Cycle.chords_subset_edgeSet {G : SimpleGraph V} (c : Cycle G) :
    c.chords ⊆ G.edgeSet := fun _ he ↦ he.1

@[simp]
lemma Cycle.mem_chords {G : SimpleGraph V} {c : Cycle G} {e : Sym2 V} :
    e ∈ c.chords ↔ e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ c.walk.support) ∧ e ∉ c.edges :=
  Iff.rfl

/-- `G` contains an odd cycle with at least `k` chords (also called diagonals). -/
def HasOddCycleWithChords (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Cycle G, Odd c.length ∧ k ≤ c.chords.encard

lemma HasOddCycleWithChords.mono {G : SimpleGraph V} {k k' : ℕ}
    (h : HasOddCycleWithChords G k) (hle : k' ≤ k) : HasOddCycleWithChords G k' := by
  obtain ⟨c, hodd, hk⟩ := h
  exact ⟨c, hodd, (Nat.cast_le.mpr hle).trans hk⟩

/-- For `k = 0`, having an odd cycle with at least `k` chords is exactly having an odd cycle. -/
lemma HasOddCycleWithChords.zero_iff {G : SimpleGraph V} :
    HasOddCycleWithChords G 0 ↔ ∃ c : Cycle G, Odd c.length :=
  ⟨fun ⟨c, hodd, _⟩ ↦ ⟨c, hodd⟩, fun ⟨c, hodd⟩ ↦ ⟨c, hodd, bot_le⟩⟩

/-- Chords are never edges of the underlying cycle walk. -/
lemma Cycle.not_mem_edges_of_mem_chords {G : SimpleGraph V} {c : Cycle G} {e : Sym2 V}
    (he : e ∈ c.chords) : e ∉ c.edges :=
  (mem_chords.mp he).2.2

/-- The set of chords is disjoint from the set of cycle edges. -/
lemma Cycle.chords_disjoint_edges {G : SimpleGraph V} (c : Cycle G) :
    Disjoint c.chords {e | e ∈ c.edges} := by
  refine Set.disjoint_left.2 fun e he ↦ ?_
  simp [not_mem_edges_of_mem_chords he]

/-- `G` is bridgeless if none of its edges is a bridge. -/
def IsBridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

/-- In a forest every edge is a bridge, so an acyclic bridgeless graph has no edges at all. -/
theorem edgeFinset_eq_empty_of_isBridgeless_of_isAcyclic [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hbr : G.IsBridgeless) : G.edgeFinset = ∅ := by
  rw [SimpleGraph.edgeFinset_eq_empty]
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hadj
  exact hbr s(u, v) hadj (G.isAcyclic_iff_forall_isBridge.mp hacyc hadj)

end SimpleGraph
