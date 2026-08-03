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

public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

/-!
# 3-Uniform Hypergraphs

This file defines the basic combinatorial infrastructure for 3-uniform hypergraphs used in
formalizations of Erdős problems (e.g., Problem 593, Problem 1177).

**Note:** Mathlib does not yet have a general hypergraph API. The definitions here fill that
gap for the special case of 3-uniform hypergraphs (every edge has exactly 3 vertices).

## Main definitions

- `ThreeUniformHypergraph V` : a set of 3-element `Finset`s on a vertex type `V`
- `ThreeUniformHypergraph.IsProperColoring` : vertex coloring with no monochromatic edge
- `ThreeUniformHypergraph.chromaticCardinal` : minimum cardinality of a color type admitting
  a proper coloring (a `Cardinal`-valued chromatic number, distinguishing infinite values)
- `ThreeUniformHypergraph.Appears` : sub-hypergraph embedding (injective vertex map
  carrying edges to edges)
- `ThreeUniformHypergraph.IsTwoColorable` : vertex set has a 2-coloring with no monochromatic
  edge (also called Property B); the 3-uniform analogue of bipartiteness for graphs
- `IsObligatory` : a finite hypergraph appears in every hypergraph of chromatic cardinal > ℵ₀

## References

- Erdős, Galvin, Hajnal, *On set-systems having large chromatic number and not containing
  prescribed subsystems*, Infinite and finite sets, 1975.
-/

open Cardinal Set

/-- A **3-uniform hypergraph** on vertex type `V` is a set of 3-element `Finset`s.
Each element of `edges` is a hyperedge, and `uniform` ensures each has exactly 3 vertices.

Note: Mathlib does not yet have a general hypergraph API; this fills that gap for the
3-uniform case relevant to Erdős problems 593 and 1177. -/
structure ThreeUniformHypergraph (V : Type) where
  /-- The set of hyperedges: each edge is a 3-element finset of vertices. -/
  edges : Set (Finset V)
  /-- Every hyperedge has exactly 3 vertices. -/
  uniform : ∀ e ∈ edges, e.card = 3

namespace ThreeUniformHypergraph

/-- A **proper coloring** of a 3-uniform hypergraph `H` by a color type `C` is a vertex
coloring such that no hyperedge is monochromatic (all three vertices receive the same color). -/
def IsProperColoring {V : Type} (H : ThreeUniformHypergraph V) {C : Type} (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- The **chromatic cardinal** of a 3-uniform hypergraph `H` is the infimum of cardinalities
of color types admitting a proper coloring.

In contrast to a `ℕ∞`-valued chromatic number, this `Cardinal`-valued definition distinguishes
between different infinite chromatic numbers (e.g., `ℵ₀` vs. `ℵ₁`). We work at `Type`
(universe 0) throughout to avoid universe metavariable issues. -/
noncomputable def chromaticCardinal {V : Type} (H : ThreeUniformHypergraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- A finite 3-uniform hypergraph `F` **appears** in `H` (as a sub-hypergraph) if there
exists an injective vertex map `φ : W → V` that sends every hyperedge of `F` to a hyperedge
of `H`. -/
def Appears {W V : Type} [DecidableEq V] (F : ThreeUniformHypergraph W)
    (H : ThreeUniformHypergraph V) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧ ∀ e ∈ F.edges, e.image φ ∈ H.edges

/-- A 3-uniform hypergraph `F` is **2-colorable** (has **Property B**) if there exists a
2-coloring of its vertices with no monochromatic edge.

This is the hypergraph analogue of bipartiteness for graphs: a graph is bipartite iff it
is 2-colorable as a graph. For 3-uniform hypergraphs, 2-colorability is a necessary condition
for being obligatory (every obligatory finite 3-uniform hypergraph is 2-colorable). -/
def IsTwoColorable {V : Type} (F : ThreeUniformHypergraph V) : Prop :=
  ∃ f : V → Fin 2, F.IsProperColoring f

end ThreeUniformHypergraph

/-- A finite 3-uniform hypergraph `F` on a `Fintype` vertex type is **obligatory** if it
appears in every 3-uniform hypergraph (on a `Type`-valued vertex set) whose chromatic
cardinal exceeds `ℵ₀`. -/
def IsObligatory {W : Type} [Fintype W] (F : ThreeUniformHypergraph W) : Prop :=
  ∀ (V : Type) [DecidableEq V] (H : ThreeUniformHypergraph V),
    ℵ₀ < H.chromaticCardinal → F.Appears H

end
