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

public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-!
# Uniform hypergraphs

A `UniformHypergraph V k` is a possibly infinite family of `k`-element finite sets.
The vertex type includes isolated vertices. Finite edge families use `Finset.IsUniform`;
`UniformHypergraph.ofFinset` converts them to this presentation.

The API includes complete subgraphs, maximal clique sizes, weak colorings, embeddings,
and chromatic cardinals. Chromatic cardinals require `2 ≤ k`, so an injective vertex
coloring always exists. Empty and singleton edges admit no weak proper coloring.
-/

open Cardinal Set

universe u

/-- A possibly infinite family of edges, each containing exactly `k` vertices. -/
structure UniformHypergraph (V : Type*) (k : ℕ) where
  /-- The set of finite hyperedges. -/
  edges : Set (Finset V)
  /-- Every hyperedge has exactly `k` vertices. -/
  uniform : ∀ e ∈ edges, e.card = k

namespace UniformHypergraph

variable {k : ℕ}

/-- A finite uniform edge family viewed as a uniform hypergraph. -/
def ofFinset {V : Type*} (H : Finset (Finset V)) (hH : H.IsUniform k) :
    UniformHypergraph V k where
  edges := (H : Set (Finset V))
  uniform := hH

@[simp]
theorem mem_edges_ofFinset {V : Type*} {H : Finset (Finset V)} {hH : H.IsUniform k}
    {e : Finset V} : e ∈ (ofFinset H hH).edges ↔ e ∈ H := Finset.mem_coe

/-- Every `k`-element subset of `S` is an edge. -/
def IsCompleteSubgraph {V : Type*} (H : UniformHypergraph V k) (S : Finset V) : Prop :=
  ∀ e : Finset V, e ⊆ S → e.card = k → e ∈ H.edges

/-- The sizes of the finite maximal complete subgraphs. -/
def cliqueSizes {V : Type*} (H : UniformHypergraph V k) : Set ℕ :=
  { n | ∃ S : Finset V, Maximal (IsCompleteSubgraph H) S ∧ S.card = n }

/-- A weak proper coloring gives two vertices different colors in every edge. -/
def IsProperColoring {V : Type*} (H : UniformHypergraph V k) {C : Type*}
    (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- An injective coloring is proper when every edge has at least two vertices. -/
theorem isProperColoring_of_injective {V C : Type*} (H : UniformHypergraph V k)
    (hk : 2 ≤ k) {f : V → C} (hf : Function.Injective f) : H.IsProperColoring f := by
  intro e he
  have hcard : 1 < e.card := by rw [H.uniform e he]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact ⟨u, hu, v, hv, fun h ↦ huv (hf h)⟩

/-- The finite and possibly infinite presentations have the same proper colorings. -/
theorem isProperColoring_ofFinset_iff {V C : Type*} (H : Finset (Finset V))
    (hH : H.IsUniform k) (f : V → C) :
    (ofFinset H hH).IsProperColoring f ↔ H.IsProperHypergraphColoring f := Iff.rfl

/-- The infimum of cardinalities of color types admitting a proper coloring.
The uniformity bound guarantees a coloring exists, even for infinite vertex types. -/
noncomputable def chromaticCardinal {V : Type u} (H : UniformHypergraph V k)
    (_hk : 2 ≤ k) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A proper coloring bounds the chromatic cardinal by the number of colors. -/
theorem chromaticCardinal_le {V C : Type u} (H : UniformHypergraph V k) (hk : 2 ≤ k)
    {f : V → C} (hf : H.IsProperColoring f) : H.chromaticCardinal hk ≤ #C :=
  csInf_le' ⟨C, rfl, f, hf⟩

/-- The vertex type itself always supplies enough colors when `2 ≤ k`. -/
theorem chromaticCardinal_le_mk {V : Type u} (H : UniformHypergraph V k) (hk : 2 ≤ k) :
    H.chromaticCardinal hk ≤ #V :=
  H.chromaticCardinal_le hk (H.isProperColoring_of_injective hk Function.injective_id)

/-- An injective vertex map carrying every edge of `F` to an edge of `H`. -/
def Appears {W V : Type*} [DecidableEq V] (F : UniformHypergraph W k)
    (H : UniformHypergraph V k) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧ ∀ e ∈ F.edges, e.image φ ∈ H.edges

/-- A two-coloring with no monochromatic edge (Property B). -/
def IsTwoColorable {V : Type*} (F : UniformHypergraph V k) : Prop :=
  ∃ f : V → Fin 2, F.IsProperColoring f

/-- Some hypergraph of the same uniformity and chromatic cardinal `κ` omits `F`. -/
def HasAvoidingChromaticCardinal {W : Type u} (F : UniformHypergraph W k)
    (hk : 2 ≤ k) (κ : Cardinal.{u}) : Prop :=
  ∃ (V : Type u) (_ : DecidableEq V) (H : UniformHypergraph V k),
    H.chromaticCardinal hk = κ ∧ ¬ F.Appears H

/-- A finite uniform hypergraph is obligatory if it appears in every hypergraph of
that uniformity whose chromatic cardinal exceeds `ℵ₀`. -/
def IsObligatory {W : Type u} [Fintype W] (F : UniformHypergraph W k) (hk : 2 ≤ k) : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : UniformHypergraph V k),
    ℵ₀ < H.chromaticCardinal hk → F.Appears H

end UniformHypergraph
