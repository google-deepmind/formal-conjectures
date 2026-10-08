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

public import Mathlib.Combinatorics.Hypergraph.Basic

@[expose] public section

/-!
# Uniformity and weak colorings of hypergraphs

This file extends Mathlib's `Hypergraph` with finite-edge constructors, uniformity,
and weak proper colorings. Uniformity uses extended cardinality, so every edge is finite,
including at uniformity zero. Empty and singleton edges admit no weak proper coloring.
-/

namespace Hypergraph

/-- Every edge has exactly `k` vertices. -/
def IsUniform {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H.edgeSet, e.encard = k

/-- A weak proper coloring gives two vertices different colors in every edge. -/
def IsProperColoring {V C : Type*} (H : Hypergraph V) (f : V → C) : Prop :=
  ∀ e ∈ H.edgeSet, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A weak proper coloring using at most `n` colors. -/
def IsNColorable {V : Type*} (H : Hypergraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, H.IsProperColoring f

/-- A family of finite edges on an explicit vertex set, retaining isolated vertices. -/
def ofEdgeFamily {V : Type*} (F : Set (Finset V)) (S : Set V)
    (h : ∀ e ∈ F, (e : Set V) ⊆ S) : Hypergraph V where
  vertexSet := S
  edgeSet := {e | ∃ a ∈ F, (a : Set V) = e}
  subset_vertexSet_of_mem_edgeSet' := by
    rintro e ⟨a, ha, rfl⟩
    exact h a ha

@[simp]
theorem mem_edgeSet_ofEdgeFamily {V : Type*} {F : Set (Finset V)} {S : Set V}
    {h : ∀ e ∈ F, (e : Set V) ⊆ S} {e : Finset V} :
    (e : Set V) ∈ (ofEdgeFamily F S h).edgeSet ↔ e ∈ F := by
  simp [ofEdgeFamily]

@[simp]
theorem isUniform_ofEdgeFamily_iff {V : Type*} {F : Set (Finset V)} {S : Set V}
    {h : ∀ e ∈ F, (e : Set V) ⊆ S} {k : ℕ} :
    (ofEdgeFamily F S h).IsUniform k ↔ ∀ e ∈ F, e.card = k := by
  simp [IsUniform, ofEdgeFamily]

@[simp]
theorem isProperColoring_ofEdgeFamily_iff {V C : Type*} {F : Set (Finset V)}
    {S : Set V} {h : ∀ e ∈ F, (e : Set V) ⊆ S} {f : V → C} :
    (ofEdgeFamily F S h).IsProperColoring f ↔
      ∀ e ∈ F, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v := by
  simp [IsProperColoring, ofEdgeFamily]

/-- Every edge of a uniform hypergraph is finite. -/
theorem IsUniform.finite_edge {V : Type*} {H : Hypergraph V} {k : ℕ}
    (hH : H.IsUniform k) {e : Set V} (he : e ∈ H.edgeSet) : e.Finite :=
  Set.finite_of_encard_eq_coe (hH e he)

/-- An injective coloring is proper when every edge has at least two vertices. -/
theorem isProperColoring_of_injective {V C : Type*} {H : Hypergraph V}
    (hH : ∀ e ∈ H.edgeSet, 2 ≤ e.encard) {f : V → C}
    (hf : Function.Injective f) : H.IsProperColoring f := by
  intro e he
  obtain ⟨u, v, hu, hv, huv⟩ := Set.one_lt_encard_iff.mp
    (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) (hH e he))
  exact ⟨u, hu, v, hv, fun h ↦ huv (hf h)⟩

/-- An injective coloring is proper when uniformity is at least two. -/
theorem IsUniform.isProperColoring_of_injective {V C : Type*} {H : Hypergraph V}
    {k : ℕ} (hH : H.IsUniform k) (hk : 2 ≤ k) {f : V → C}
    (hf : Function.Injective f) : H.IsProperColoring f := by
  apply Hypergraph.isProperColoring_of_injective ?_ hf
  intro e he
  rw [hH e he]
  exact_mod_cast hk

end Hypergraph
