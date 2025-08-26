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

import Mathlib.Combinatorics.SimpleGraph.Clique

/-
Dominating sets and domination numbers

This file introduces dominating sets and related invariants.

Main definitions

* `SimpleGraph.IsDominating`   : A set of vertices that dominates all vertices.
* `SimpleGraph.IsNDominatingSet` : A dominating set with `n` vertices.
* `SimpleGraph.dominationNumber` : The domination number of a graph.
* `SimpleGraph.IsTotalDominating` : A total dominating set.
* `SimpleGraph.IsTotalNDominatingSet` : A total dominating set with `n` vertices.
* `SimpleGraph.totalDominationNumber` : The total domination number.

Future work should extend this file with connected, independent, and power
variants as well as domination-related lemmas.
-/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

/-! ### Dominating sets -/

/-- A set `D` is a dominating set for `G` if every vertex of `G` is either in
`D` or adjacent to a vertex of `D`. -/
def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- An `n`-dominating set is a dominating set with `n` vertices. -/
@[mk_iff]
structure IsNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isDominating : G.IsDominating D
  card_eq : D.card = n

/-! ### Domination number -/

/-- The domination number of a graph `G` is the minimum size of a dominating
set. It is `0` if there are no vertices. -/
noncomputable def dominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNDominatingSet n D}

/-! ### Total domination -/

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

/-! ### Connected domination -/

/-- A set is a connected dominating set if it is dominating and induces a
connected subgraph. -/
def IsConnectedDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  G.IsDominating D ∧ (G.induce D).Connected

/-- The connected domination number of `G`. -/
noncomputable def connectedDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsConnectedDominating (D : Set α) ∧ D.card = n}

/-! ### Independent domination -/

def IsIndepDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  G.IsIndepSet D ∧ G.IsDominating D

@[mk_iff]
structure IsNIndepDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}

/-! ### Vertex and edge covers -/

/-- A set of vertices is a vertex cover if every edge has an endpoint in it. -/
def IsVertexCover (G : SimpleGraph α) (C : Set α) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The vertex cover number of `G`. -/
noncomputable def vertexCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ C : Finset α, G.IsVertexCover (C : Set α) ∧ C.card = n}

/-- A set of edges is an edge cover if every vertex is incident to some edge in it. -/
def IsEdgeCover (G : SimpleGraph α) (M : Set (Sym2 α)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ v, ∃ e ∈ M, v ∈ e

/-- The minimum edge cover number of `G`. -/
noncomputable def edgeCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsEdgeCover (M : Set (Sym2 α)) ∧ M.card = n}

/-! ### Edge domination -/

def edgesAdjacent (e e' : Sym2 α) : Prop := ∃ v, v ∈ e ∧ v ∈ e'

def IsEdgeDominating (G : SimpleGraph α) (M : Set (Sym2 α)) : Prop :=
  ∀ ⦃e⦄, e ∈ G.edgeSet → e ∈ M ∨ ∃ e' ∈ M, edgesAdjacent e e'

@[mk_iff]
structure IsNEdgeDominatingSet (n : ℕ) (M : Finset (Sym2 α)) : Prop where
  isDominating : G.IsEdgeDominating (M : Set (Sym2 α))
  card_eq : M.card = n

noncomputable def edgeDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsNEdgeDominatingSet n M}

end SimpleGraph
