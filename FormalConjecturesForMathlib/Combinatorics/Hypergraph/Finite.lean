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

public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.ENat.Lattice
public import FormalConjecturesForMathlib.Combinatorics.SetFamily.PropertyB

@[expose] public section

/-!
# Finite hypergraphs and block designs

Finite hypergraphs are finite families of finite vertex sets. This file supplies uniformity,
weak vertex coloring, independent sets, transversals, designs, and finite extremal counts.
`Finset.toHypergraph` connects this presentation to Mathlib's `Hypergraph`.

The ground type includes isolated vertices. The support is `H.biUnion id` when only incident
vertices should be counted. Colorings require two differently colored vertices in every edge;
empty and singleton edges therefore admit no proper coloring.
-/

namespace Set

/-- A family of finite sets has a transversal with at most `k` vertices. -/
def HasFiniteTransversal {V : Type*} (F : Set (Finset V)) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ ∀ e ∈ F, ∃ v ∈ S, v ∈ e

end Set

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The hypergraph with edge family `H` and ground vertex set `S`. -/
def toHypergraph (H : Finset (Finset V)) (S : Finset V) (h : ∀ e ∈ H, e ⊆ S) :
    Hypergraph V :=
  Hypergraph.ofEdgeFamily (H : Set (Finset V)) S h

omit [DecidableEq V] in
/-- Conversion preserves uniformity. -/
@[simp]
theorem isUniform_toHypergraph_iff (H : Finset (Finset V)) (S : Finset V)
    (h : ∀ e ∈ H, e ⊆ S) (r : ℕ) :
    (H.toHypergraph S h).IsUniform r ↔ H.IsUniform r := by
  exact Hypergraph.isUniform_ofEdgeFamily_iff

/-- A weak proper coloring has no monochromatic edge. -/
def IsProperHypergraphColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

omit [DecidableEq V] in
/-- Conversion preserves weak proper colorings. -/
@[simp]
theorem isProperColoring_toHypergraph_iff {C : Type*} (H : Finset (Finset V))
    (S : Finset V) (h : ∀ e ∈ H, e ⊆ S) (f : V → C) :
    (H.toHypergraph S h).IsProperColoring f ↔ H.IsProperHypergraphColoring f := by
  exact Hypergraph.isProperColoring_ofEdgeFamily_iff

/-- The edge family admits a weak proper coloring with `k` colors. -/
def HypergraphColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, H.IsProperHypergraphColoring c

omit [DecidableEq V] in
/-- Two-colorability agrees with the existing Property B predicate. -/
theorem hypergraphColorable_two_iff (H : Finset (Finset V)) :
    H.HypergraphColorable 2 ↔ H.HasPropertyB := Iff.rfl

/-- The weak chromatic number is exactly `k`. -/
def HasHypergraphChromaticNumber (H : Finset (Finset V)) (k : ℕ) : Prop :=
  H.HypergraphColorable k ∧ ∀ j < k, ¬ H.HypergraphColorable j

/-- No edge is contained in this set of vertices. -/
def IsHypergraphIndependent (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ S

/-- The number of hyperedges containing a vertex. -/
def hypergraphDegree (H : Finset (Finset V)) (v : V) : ℕ := #{e ∈ H | v ∈ e}

/-- Distinct edges intersect in at most one vertex. -/
def IsLinearHypergraph (H : Finset (Finset V)) : Prop :=
  (H : Set (Finset V)).Pairwise fun e f ↦ (e ∩ f).card ≤ 1

/-- Some `m` vertices span at least `k` edges. -/
def ContainsSubgraph (H : Finset (Finset V)) (m k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = m ∧ k ≤ #{e ∈ H | e ⊆ S}

/-- The edges induced on a vertex set. -/
def hypergraphInduce (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter (· ⊆ S)

/-- A copy of the complete `r`-uniform hypergraph on `k` vertices. -/
def ContainsCompleteHypergraph (H : Finset (Finset V)) (r k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ S.powersetCard r ⊆ H

/-- A collection of `k` pairwise vertex-disjoint edges. -/
def HasHypergraphMatching (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ M ⊆ H, M.card = k ∧ (M : Set (Finset V)).Pairwise Disjoint

/-- Every `t`-set of ground vertices lies in exactly one block. -/
def IsBlockDesign (H : Finset (Finset V)) (t k : ℕ) : Prop :=
  H.IsUniform k ∧ ∀ S : Finset V, S.card = t → ∃! e, e ∈ H ∧ S ⊆ e

/-- A pairwise balanced design, permitting a block equal to the ground set. -/
def IsPairwiseBalancedDesign (H : Finset (Finset V)) : Prop :=
  (∀ e ∈ H, 2 ≤ e.card) ∧
    ∀ S : Finset V, S.card = 2 → ∃! e, e ∈ H ∧ S ⊆ e

/-- The nondecreasing block-size sequence, retaining repeated sizes. -/
def blockSizeProfile (H : Finset (Finset V)) : List ℕ :=
  (H.val.map Finset.card).sort (· ≤ ·)

/-- Partition into complete `r`-graphs with either `r` or `r+1` vertices. -/
def IsCompleteHypergraphDecomposition (H : Finset (Finset V)) (r : ℕ)
    (D : Finset (Finset V)) : Prop :=
  (∀ S ∈ D, S.card = r ∨ S.card = r + 1) ∧
    H = D.biUnion (fun S ↦ S.powersetCard r) ∧
    (D : Set (Finset V)).Pairwise fun S T ↦ Disjoint (S.powersetCard r) (T.powersetCard r)

/-- A complete `t`-partite `t`-uniform hypergraph with `r` vertices in each part. -/
def ContainsCompletePartiteHypergraph (H : Finset (Finset V)) (t r : ℕ) : Prop :=
  ∃ f : Fin t × Fin r ↪ V, ∀ a : Fin t → Fin r,
    (Finset.univ.image fun i ↦ f (i, a i)) ∈ H

/-- Two distinct disjoint pairs of edges with the same union. -/
def HasRepeatedDisjointUnion (H : Finset (Finset V)) : Prop :=
  ∃ A ∈ H, ∃ B ∈ H, ∃ C ∈ H, ∃ D ∈ H,
    Disjoint A B ∧ Disjoint C D ∧ A ∪ B = C ∪ D ∧
    A ≠ B ∧ C ≠ D ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D

omit [DecidableEq V] in
@[simp] theorem isUniform_empty (r : ℕ) : (∅ : Finset (Finset V)).IsUniform r := by
  simp [IsUniform]

/-- The cardinal bound in `ContainsSubgraph` counts edges, not copies with labels. -/
theorem containsSubgraph_iff (H : Finset (Finset V)) (m k : ℕ) :
    H.ContainsSubgraph m k ↔ ∃ S : Finset V,
      S.card = m ∧ k ≤ (H.hypergraphInduce S).card := Iff.rfl

omit [DecidableEq V] in
/-- A singleton edge prevents any weak proper coloring. -/
theorem not_colorable_singleton (v : V) (k : ℕ) :
    ¬ ({ {v} } : Finset (Finset V)).HypergraphColorable k := by
  rintro ⟨c, hc⟩
  simp [IsProperHypergraphColoring] at hc

open scoped Classical in
/-- The largest cardinality of an independent vertex set in a finite ground type. -/
noncomputable def hypergraphIndependenceNumber [Fintype V] (H : Finset (Finset V)) : ℕ :=
  ((Finset.univ : Finset V).powerset.filter H.IsHypergraphIndependent).sup Finset.card

open scoped Classical in
/-- Subsets of the incident vertices witnessing Property B. -/
noncomputable def propertyBWitnesses (H : Finset (Finset V)) : Finset (Finset V) :=
  (H.biUnion id).powerset.filter fun B ↦
    (∀ e ∈ H, (e ∩ B).Nonempty) ∧ H.IsHypergraphIndependent B

end Finset

namespace Hypergraph

open scoped Classical in
/-- Maximum number of edges among `r`-uniform families satisfying `P` on `n` labeled vertices.
The value is zero if no family is admissible. -/
noncomputable def extremalNumber (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard r).powerset.filter P).sup Finset.card

/-- The extremal number forbidding a complete uniform hypergraph. -/
noncomputable def cliqueExtremalNumber (n r k : ℕ) : ℕ :=
  extremalNumber n r fun H ↦ ¬ H.ContainsCompleteHypergraph r k

/-- The extremal number forbidding `e` edges on `v` vertices (not necessarily induced). -/
noncomputable def configurationExtremalNumber (n r v e : ℕ) : ℕ :=
  extremalNumber n r fun H ↦ ¬ H.ContainsSubgraph v e

/-- The extremal number forbidding a complete balanced multipartite uniform hypergraph. -/
noncomputable def partiteExtremalNumber (n t r : ℕ) : ℕ :=
  extremalNumber n t fun H ↦ ¬ H.ContainsCompletePartiteHypergraph t r

/-- Minimum edge count for chromatic number `k`, with infinity when no such graph exists. -/
noncomputable def minChromaticEdges (r k : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (H : Finset (Finset (Fin n))) (_ : H.IsUniform r)
    (_ : H.HasHypergraphChromaticNumber k), (H.card : ℕ∞)

open scoped Classical in
/-- All block-size sequences of pairwise balanced designs on `n` labeled vertices. -/
noncomputable def blockSizeProfiles (n : ℕ) : Finset (List ℕ) :=
  (((Finset.univ : Finset (Fin n)).powerset.powerset).filter
    Finset.IsPairwiseBalancedDesign).image Finset.blockSizeProfile

end Hypergraph
