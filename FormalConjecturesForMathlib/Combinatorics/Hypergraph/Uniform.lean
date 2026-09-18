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

A `UniformHypergraph V k` extends Mathlib's `Hypergraph V` with uniformity `k`
and vertex set `Set.univ`. The vertex type includes isolated vertices.
Finite edge families use `Finset.IsUniform`;
`UniformHypergraph.ofFinset` converts them to this presentation.

The API includes complete subgraphs, maximal clique sizes, weak colorings, embeddings,
and chromatic cardinals. The chromatic cardinal is zero when no proper coloring exists.
Empty and singleton edges admit no weak proper coloring.
-/

open Cardinal Set

universe u

/-- A uniform Mathlib hypergraph whose vertex set is the entire ambient type. -/
structure UniformHypergraph (V : Type*) (k : ℕ) extends Hypergraph V where
  /-- All elements of the vertex type are vertices, including isolated ones. -/
  vertexSet_eq_univ : vertexSet = Set.univ
  /-- Every hyperedge has exactly `k` vertices. -/
  uniform : toHypergraph.IsUniform k

namespace UniformHypergraph

variable {k : ℕ}

/-- A finite uniform edge family viewed as a uniform hypergraph. -/
def ofFinset {V : Type*} (H : Finset (Finset V)) (hH : H.IsUniform k) :
    UniformHypergraph V k where
  toHypergraph := Hypergraph.ofEdgeFamily (H : Set (Finset V)) Set.univ
    (fun _ _ ↦ Set.subset_univ _)
  vertexSet_eq_univ := rfl
  uniform := Hypergraph.isUniform_ofEdgeFamily_iff.mpr hH

@[simp]
theorem mem_edgeSet_ofFinset {V : Type*} {H : Finset (Finset V)} {hH : H.IsUniform k}
    {e : Finset V} : (e : Set V) ∈ (ofFinset H hH).edgeSet ↔ e ∈ H :=
  Hypergraph.mem_edgeSet_ofEdgeFamily (h := fun _ _ ↦ Set.subset_univ _)

/-- Every `k`-element subset of `S` is an edge. -/
def IsCompleteOn {V : Type*} (H : UniformHypergraph V k) (S : Finset V) : Prop :=
  ∀ e : Finset V, e ⊆ S → e.card = k → (e : Set V) ∈ H.edgeSet

/-- The sizes of the finite maximal complete subgraphs. -/
def cliqueSizes {V : Type*} (H : UniformHypergraph V k) : Set ℕ :=
  { n | ∃ S : Finset V, Maximal (IsCompleteOn H) S ∧ S.card = n }

/-- Weak proper coloring of the underlying Mathlib hypergraph. -/
abbrev IsProperColoring {V : Type*} (H : UniformHypergraph V k) {C : Type*}
    (f : V → C) : Prop :=
  H.toHypergraph.IsProperColoring f

/-- An injective coloring is proper when every edge has at least two vertices. -/
theorem isProperColoring_of_injective {V C : Type*} (H : UniformHypergraph V k)
    (hk : 2 ≤ k) {f : V → C} (hf : Function.Injective f) : H.IsProperColoring f :=
  H.uniform.isProperColoring_of_injective hk hf

/-- The finite and possibly infinite presentations have the same proper colorings. -/
theorem isProperColoring_ofFinset_iff {V C : Type*} (H : Finset (Finset V))
    (hH : H.IsUniform k) (f : V → C) :
    (ofFinset H hH).IsProperColoring f ↔ H.IsProperHypergraphColoring f := by
  exact Hypergraph.isProperColoring_ofEdgeFamily_iff (h := fun _ _ ↦ Set.subset_univ _)

/-- The infimum of cardinalities of color types admitting a proper coloring.
The value is zero when no proper coloring exists. -/
noncomputable def chromaticCardinal {V : Type u} (H : UniformHypergraph V k) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A proper coloring bounds the chromatic cardinal by the number of colors. -/
theorem chromaticCardinal_le {V C : Type u} (H : UniformHypergraph V k)
    {f : V → C} (hf : H.IsProperColoring f) : H.chromaticCardinal ≤ #C :=
  csInf_le' ⟨C, rfl, f, hf⟩

/-- The vertex type itself always supplies enough colors when `2 ≤ k`. -/
theorem chromaticCardinal_le_mk {V : Type u} (H : UniformHypergraph V k) (hk : 2 ≤ k) :
    H.chromaticCardinal ≤ #V :=
  H.chromaticCardinal_le (H.isProperColoring_of_injective hk Function.injective_id)

/-- An injective vertex map carrying every edge of `F` to an edge of `H`. -/
def Appears {W V : Type*} (F : UniformHypergraph W k)
    (H : UniformHypergraph V k) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧
    (F.toHypergraph.image φ).edgeSet ⊆ H.edgeSet

/-- Appearance is transitive under composition of injective vertex maps. -/
theorem Appears.trans {U W V : Type*} {F : UniformHypergraph U k}
    {G : UniformHypergraph W k} {H : UniformHypergraph V k}
    (hFG : F.Appears G) (hGH : G.Appears H) : F.Appears H := by
  obtain ⟨f, hf, hF⟩ := hFG
  obtain ⟨g, hg, hG⟩ := hGH
  refine ⟨g ∘ f, hg.comp hf, ?_⟩
  rw [← Hypergraph.image_image]
  exact (Set.image_mono hF).trans hG

/-- A weak proper coloring using at most `n` colors. -/
abbrev IsNColorable {V : Type*} (F : UniformHypergraph V k) (n : ℕ) : Prop :=
  F.toHypergraph.IsNColorable n

/-- Some hypergraph of the same uniformity and chromatic cardinal `κ` omits `F`. -/
def HasAvoidingChromaticCardinal {W : Type u} (F : UniformHypergraph W k)
    (κ : Cardinal.{u}) : Prop :=
  ∃ (V : Type u) (_ : DecidableEq V) (H : UniformHypergraph V k),
    H.chromaticCardinal = κ ∧ ¬ F.Appears H

/-- A finite uniform hypergraph is obligatory if it appears in every hypergraph of
that uniformity whose chromatic cardinal exceeds `ℵ₀`. -/
def IsObligatory {W : Type u} [Fintype W] (F : UniformHypergraph W k) : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : UniformHypergraph V k),
    ℵ₀ < H.chromaticCardinal → F.Appears H

end UniformHypergraph
