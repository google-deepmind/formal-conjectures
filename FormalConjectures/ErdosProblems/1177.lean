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
# Erdős Problem 1177

*Reference:* [erdosproblems.com/1177](https://www.erdosproblems.com/1177)

Let $G$ be a finite $3$-uniform hypergraph, and let $F_G(\kappa)$ denote the collection of
$3$-uniform hypergraphs with chromatic number $\kappa$ not containing $G$.

A problem of Erdős, Galvin, and Hajnal.

[Va99] is the source reference for all parts (Section 7.94).
-/

open Cardinal

namespace Erdos1177

/-- A proper coloring of a $3$-uniform hypergraph with vertex type $V$ using colors from $\alpha$
    is a function $c : V \to \alpha$ such that no hyperedge is monochromatic: for every edge $e$
    there exist two vertices in $e$ assigned different colors. -/
def IsProperColoring3 {V α : Type*} (edges : Set (Finset V)) (c : V → α) : Prop :=
  ∀ e ∈ edges, ∃ v ∈ e, ∃ w ∈ e, c v ≠ c w

/-- A $3$-uniform hypergraph (on vertex type $V$, with edge set `edges`) has cardinal chromatic
    number $\kappa$ if $\kappa$ is the least cardinality of a color set admitting a proper coloring:
    - there exists a proper coloring with a color set of cardinality $\le \kappa$, and
    - every proper coloring requires a color set of cardinality $\ge \kappa$. -/
def HasChromaticNumber3 {V : Type} (edges : Set (Finset V)) (κ : Cardinal.{0}) : Prop :=
  (∃ (α : Type), #α ≤ κ ∧ ∃ c : V → α, IsProperColoring3 edges c) ∧
  ∀ (α : Type), (∃ c : V → α, IsProperColoring3 edges c) → κ ≤ #α

/-- $H$ is $G$-free if there is no injective map $f : V_G \to V_H$ sending every edge of $G$ to an
    edge of $H$ (i.e., $G$ does not embed as a sub-hypergraph of $H$). Each edge of $G$ maps to
    an edge of $H$ via $f$ when the image of the edge under $f$ equals an edge of $H$ as a
    set. -/
def IsFreeOf {VG VH : Type*} (edgesG : Set (Finset VG)) (edgesH : Set (Finset VH)) : Prop :=
  ¬ ∃ f : VG → VH, Function.Injective f ∧
    ∀ e ∈ edgesG, ∃ e' ∈ edgesH, (↑e' : Set VH) = f '' (↑e : Set VG)

/--
Erdős Problem 1177, Part 1 [Va99, 7.94]:

Let $G$ be a finite $3$-uniform hypergraph. If $F_G(\aleph_1)$ is non-empty (i.e., there exists
a $G$-free $3$-uniform hypergraph with chromatic number $\aleph_1$), then there exists
$X \in F_G(\aleph_1)$ with vertex set of cardinality at most $2^{2^{\aleph_0}}$.

A problem of Erdős, Galvin, and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1177
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (edgesG_finite : edgesG.Finite) (hG : ∀ e ∈ edgesG, e.card = 3)
    (h : ∃ (VH : Type) (edgesH : Set (Finset VH)),
      (∀ e ∈ edgesH, e.card = 3) ∧
      HasChromaticNumber3 edgesH (aleph 1) ∧
      IsFreeOf edgesG edgesH) :
    ∃ (VH : Type) (edgesH : Set (Finset VH)),
      (∀ e ∈ edgesH, e.card = 3) ∧
      HasChromaticNumber3 edgesH (aleph 1) ∧
      IsFreeOf edgesG edgesH ∧
      #VH ≤ (2 : Cardinal.{0}) ^ (2 : Cardinal.{0}) ^ aleph 0 := by
  sorry

/--
Erdős Problem 1177, Part 2 [Va99, 7.94]:

Let $G$ and $H$ be finite $3$-uniform hypergraphs. If $F_G(\aleph_1)$ and $F_H(\aleph_1)$ are both
non-empty, then $F_G(\aleph_1) \cap F_H(\aleph_1)$ is non-empty: there exists a $3$-uniform
hypergraph with chromatic number $\aleph_1$ that contains neither $G$ nor $H$ as a
sub-hypergraph.

A problem of Erdős, Galvin, and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1177.variants.intersection
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (edgesG_finite : edgesG.Finite) (hG : ∀ e ∈ edgesG, e.card = 3)
    {VH : Type} [Fintype VH] (edgesH : Set (Finset VH))
    (edgesH_finite : edgesH.Finite) (hH : ∀ e ∈ edgesH, e.card = 3)
    (hFG : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesG edgesW)
    (hFH : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesH edgesW) :
    ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesG edgesW ∧ IsFreeOf edgesH edgesW := by
  sorry

/--
Erdős Problem 1177, Part 3 [Va99, 7.94]:

Let $G$ be a finite $3$-uniform hypergraph. If $\kappa$ and $\mu$ are uncountable cardinals
(both $\ge \aleph_1$) and $F_G(\kappa)$ is non-empty, then $F_G(\mu)$ is non-empty: the existence
of a $G$-free $3$-uniform hypergraph with chromatic number $\kappa$ implies the existence of one
with chromatic number $\mu$.

A problem of Erdős, Galvin, and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1177.variants.cardinal_transfer
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (edgesG_finite : edgesG.Finite) (hG : ∀ e ∈ edgesG, e.card = 3)
    (κ μ : Cardinal.{0}) (hκ : aleph 1 ≤ κ) (hμ : aleph 1 ≤ μ)
    (h : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW κ ∧
      IsFreeOf edgesG edgesW) :
    ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW μ ∧
      IsFreeOf edgesG edgesW := by
  sorry

end Erdos1177
