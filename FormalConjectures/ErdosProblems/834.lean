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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 834

*Reference:* [erdosproblems.com/834](https://www.erdosproblems.com/834)

Does there exist a $3$-critical $3$-uniform hypergraph in which every vertex
has degree $\geq 7$? A problem of Erdős and Lovász [Er74d].

There are two natural interpretations of "$3$-critical":

1. **Transversal criticality**: the minimum transversal (hitting set) has
   size $3$, and for every edge $e$ the hypergraph $H \setminus \{e\}$ has a transversal
   of size $\leq 2$.

2. **Chromatic criticality**: the chromatic number is $3$, but deleting any
   edge or vertex reduces the chromatic number to at most $2$.

Li [Li25] resolved both formulations:
- In the transversal formulation, every $3$-critical $3$-uniform hypergraph
  has a vertex of degree $\leq 6$ (answer: NO).
- In the chromatic formulation, there exists a $3$-critical $3$-uniform
  hypergraph on $9$ vertices with minimum degree $7$ (answer: YES).

[Er74d, p.282] Erdős, P. and Lovász, L., _Problems and results on 3-chromatic hypergraphs
and some related questions_. Infinite and Finite Sets, Colloq. Math. Soc. J. Bolyai **10**
(1975), 609–627.

[Li25] Li, R., _On an Erdős-Lovász problem: 3-critical 3-graphs of minimum degree 7_.
arXiv:2512.24850 (2025).
-/

open Finset

namespace Erdos834

/-- A hypergraph on vertex type $V$, represented as a finset of edges,
where each edge is a finset of vertices. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)

/-- A hypergraph is $r$-uniform if every edge has exactly $r$ vertices. -/
def Hypergraph.IsUniform {V : Type*} [DecidableEq V] (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- The degree of a vertex $v$ in a hypergraph is the number of edges containing $v$. -/
def Hypergraph.degree {V : Type*} [DecidableEq V] (H : Hypergraph V) (v : V) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

/-- The vertices of a hypergraph (the union of all edges). -/
def Hypergraph.vertices {V : Type*} [DecidableEq V] (H : Hypergraph V) : Finset V :=
  H.edges.biUnion id

/-- The hypergraph obtained by removing an edge. -/
def Hypergraph.eraseEdge {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (e : Finset V) : Hypergraph V :=
  ⟨H.edges.erase e⟩

/-- The hypergraph obtained by removing a vertex (and all edges containing it). -/
def Hypergraph.eraseVertex {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (v : V) : Hypergraph V :=
  ⟨H.edges.filter (fun e => v ∉ e)⟩

/-- A proper coloring of a hypergraph: no edge is monochromatic. -/
def Hypergraph.IsProperColoring {V : Type*} [DecidableEq V] (H : Hypergraph V)
    {α : Type*} (f : V → α) : Prop :=
  ∀ e ∈ H.edges, e.card ≥ 2 → ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A set $S$ is a transversal (hitting set) of $H$ if it intersects every edge. -/
def Hypergraph.IsTransversal {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (S : Finset V) : Prop :=
  ∀ e ∈ H.edges, ∃ v ∈ e, v ∈ S

/-- A hypergraph is $3$-transversal-critical if the minimum transversal has
size $3$ and removing any single edge allows a transversal of size $\leq 2$. -/
def Hypergraph.Is3TransversalCritical {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : Prop :=
  (∃ S : Finset V, S.card = 3 ∧ H.IsTransversal S) ∧
  (∀ S : Finset V, S.card < 3 → ¬H.IsTransversal S) ∧
  (∀ e ∈ H.edges, ∃ S : Finset V, S.card ≤ 2 ∧ (H.eraseEdge e).IsTransversal S)

/-- A hypergraph is $3$-chromatic-critical if its chromatic number is $3$ and
removing any edge or vertex makes it $2$-colorable. -/
def Hypergraph.Is3ChromaticCritical {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : Prop :=
  (∃ f : V → Fin 3, H.IsProperColoring f) ∧
  (∀ f : V → Fin 2, ¬H.IsProperColoring f) ∧
  (∀ e ∈ H.edges, ∃ f : V → Fin 2, (H.eraseEdge e).IsProperColoring f) ∧
  (∀ v : V, v ∈ H.vertices → ∃ f : V → Fin 2, (H.eraseVertex v).IsProperColoring f)

/--
Erdős Problem 834, transversal formulation (resolved by Li [Li25]):

Does there exist a $3$-transversal-critical $3$-uniform hypergraph in which every vertex
has degree $\geq 7$? Li showed the answer is NO: every such hypergraph has a vertex
of degree $\leq 6$.
-/
@[category research solved, AMS 5]
theorem erdos_834 : answer(False) ↔
    ∃ (n : ℕ) (H : Hypergraph (Fin n)), H.IsUniform 3 ∧ H.Is3TransversalCritical ∧
      ∀ v : Fin n, H.degree v ≥ 7 := by
  sorry

/--
Erdős Problem 834, chromatic formulation (resolved by Li [Li25]):

Does there exist a $3$-chromatic-critical $3$-uniform hypergraph in which every vertex
has degree $\geq 7$? Li showed the answer is YES, constructing such a hypergraph
on $9$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_834.variants.chromatic : answer(True) ↔
    ∃ (n : ℕ) (H : Hypergraph (Fin n)), H.IsUniform 3 ∧ H.Is3ChromaticCritical ∧
      ∀ v : Fin n, H.degree v ≥ 7 := by
  sorry

end Erdos834
