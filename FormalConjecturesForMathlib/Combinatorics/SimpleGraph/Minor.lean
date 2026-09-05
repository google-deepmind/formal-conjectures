-- NOTE: this file is a copy taken on 2026-09-04 from the open pull request #5196
-- ("Add graph minors (ForMathlib) and Hadwiger's conjecture", branch
-- henrykmichalewski:hadwiger). It is included here so the minor-dependent
-- conjectures (Neumann-Lara, Tait) build before #5196 is merged.
-- If the original in #5196 (or wherever `SimpleGraph.IsMinor` eventually lands
-- in the repo/Mathlib) changes, the upstream version should be used instead of
-- this copy, and this note removed.
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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# Graph minors

Mathlib has no notion of graph minor (as of 2026-08). This file defines `SimpleGraph.IsMinor`
through **minor models**: `H` is a minor of `G` if there are pairwise disjoint, nonempty,
connected *branch sets* `B w ⊆ V(G)`, one for each vertex `w` of `H`, such that every edge
`w w'` of `H` is witnessed by an edge of `G` between `B w` and `B w'`. This is the standard
characterisation of `H ≼ G` (obtained from a subgraph of `G` by contracting the branch sets).

We prove that the relation is reflexive and preserved under taking supergraphs of `G` and
subgraphs of `H`.
-/

namespace SimpleGraph

variable {V W : Type*}

/-- A **minor model** of `H` in `G`: pairwise disjoint, nonempty, connected branch sets
`B w ⊆ V(G)` indexed by the vertices of `H`, with every edge of `H` realised by an edge of `G`
between the corresponding branch sets. -/
structure IsMinorModel (H : SimpleGraph W) (G : SimpleGraph V) (B : W → Set V) : Prop where
  nonempty : ∀ w, (B w).Nonempty
  connected : ∀ w, (G.induce (B w)).Connected
  disjoint : ∀ w w', w ≠ w' → Disjoint (B w) (B w')
  adj : ∀ w w', H.Adj w w' → ∃ u ∈ B w, ∃ v ∈ B w', G.Adj u v

/-- `H` is a **minor** of `G` if it has a minor model in `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V, IsMinorModel H G B

@[inherit_doc] scoped infixl:50 " ≼ " => IsMinor

/-- The singleton branch sets form a minor model of `G` in itself. -/
theorem isMinorModel_singleton (G : SimpleGraph V) :
    IsMinorModel G G (fun v => {v}) where
  nonempty v := Set.singleton_nonempty v
  connected v := by
    rw [connected_iff]
    refine ⟨?_, ⟨⟨v, Set.mem_singleton v⟩⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain rfl := Set.mem_singleton_iff.mp ha
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact Reachable.refl _
  disjoint v w hvw := Set.disjoint_singleton.mpr hvw
  adj v w h := ⟨v, Set.mem_singleton v, w, Set.mem_singleton w, h⟩

/-- Every graph is a minor of itself. -/
theorem IsMinor.refl (G : SimpleGraph V) : G.IsMinor G :=
  ⟨_, isMinorModel_singleton G⟩

/-- A minor model stays a minor model if the host graph grows. -/
theorem IsMinorModel.mono_right {H : SimpleGraph W} {G G' : SimpleGraph V} {B : W → Set V}
    (hG : G ≤ G') (hB : IsMinorModel H G B) : IsMinorModel H G' B where
  nonempty := hB.nonempty
  connected w := (hB.connected w).mono fun _ _ h => hG h
  disjoint := hB.disjoint
  adj w w' h := by
    obtain ⟨u, hu, v, hv, huv⟩ := hB.adj w w' h
    exact ⟨u, hu, v, hv, hG huv⟩

/-- A minor model of `H` is a minor model of any subgraph of `H` (on the same vertex set). -/
theorem IsMinorModel.mono_left {H H' : SimpleGraph W} {G : SimpleGraph V} {B : W → Set V}
    (hH : H' ≤ H) (hB : IsMinorModel H G B) : IsMinorModel H' G B where
  nonempty := hB.nonempty
  connected := hB.connected
  disjoint := hB.disjoint
  adj w w' h := hB.adj w w' (hH h)

/-- If `H ≼ G` and `G ≤ G'` then `H ≼ G'`. -/
theorem IsMinor.mono_right {H : SimpleGraph W} {G G' : SimpleGraph V} (hG : G ≤ G')
    (h : H.IsMinor G) : H.IsMinor G' :=
  h.imp fun _ hB => hB.mono_right hG

/-- If `H' ≤ H` and `H ≼ G` then `H' ≼ G`. -/
theorem IsMinor.mono_left {H H' : SimpleGraph W} {G : SimpleGraph V} (hH : H' ≤ H)
    (h : H.IsMinor G) : H'.IsMinor G :=
  h.imp fun _ hB => hB.mono_left hH

/-- Every subgraph (on the same vertex set) is a minor. -/
theorem IsMinor.of_le {G G' : SimpleGraph V} (h : G ≤ G') : G.IsMinor G' :=
  (IsMinor.refl G).mono_right h

/-- A minor of a finite graph has at most as many vertices. -/
theorem IsMinor.card_le [Fintype V] [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    (h : H.IsMinor G) : Fintype.card W ≤ Fintype.card V := by
  classical
  obtain ⟨B, hB⟩ := h
  choose f hf using hB.nonempty
  refine Fintype.card_le_of_injective f fun w w' hww' => ?_
  by_contra hne
  exact Set.disjoint_left.mp (hB.disjoint w w' hne) (hf w) (hww' ▸ hf w')

end SimpleGraph
