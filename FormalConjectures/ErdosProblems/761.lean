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

public import FormalConjecturesUtil

/-!
# Erdős Problem 761

*References:*
- [erdosproblems.com/761](https://www.erdosproblems.com/761)
- [ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory*.
  Quo vadis, graph theory? (1993), 261-264.
-/

@[expose] public section

universe u

namespace Erdos761

/-- The vertices in `S` span no directed cycle of `D`: there is no closed directed walk of
positive length inside `S`. -/
def IsAcyclicOn {V : Type*} (D : Digraph V) (S : Set V) : Prop :=
  ∀ v : V, ¬ Relation.TransGen (fun a b : V ↦ a ∈ S ∧ b ∈ S ∧ D.Adj a b) v v

/-- `Dicolorable G k` says that, for every orientation `D` of `G`, the vertices can be coloured
with `k` colours such that no colour class contains a directed cycle of `D`. -/
def Dicolorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ D : Digraph V, D.IsOrientation G →
    ∃ c : V → Fin k, ∀ i : Fin k, IsAcyclicOn D {v | c v = i}

/-- The dichromatic number $\delta(G)$: the least `k` such that `G` is `k`-dicolorable. It is
finite for finite graphs, since colouring all vertices differently works. -/
noncomputable def dichromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : Dicolorable G k), (k : ℕ∞)

/-- If `Dicolorable G k` holds, then $\delta(G) \leq k$. -/
@[category API, AMS 5]
theorem dichromaticNumber_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : Dicolorable G k) : dichromaticNumber G ≤ k :=
  iInf₂_le k h

/--
The dichromatic number of $G$, denoted by $\delta(G)$, is the minimum number $k$ of colours
required such that, in any orientation of the edges of $G$, there is a $k$-colouring of the
vertices of $G$ such that there are no monochromatic oriented cycles.

Must a graph with large chromatic number have large dichromatic number?

This question is due to Erdős and Neumann-Lara. We read it for finite graphs: for every $k$ there
is $m$ such that every finite graph with $\chi(G)\geq m$ has $\delta(G)\geq k$.
-/
@[category research open, question, AMS 5]
theorem erdos_761.parts.i :
    ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ dichromaticNumber G := by
  sorry

/--
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to
colour the vertices of $G$ such that each colour class induces either a complete graph or empty
graph.

Must a graph with large cochromatic number contain a graph with large dichromatic number?

This question is due to Erdős and Gimbel. We read it for finite graphs and subgraphs: for every
$k$ there is $m$ such that every finite graph with $\zeta(G)\geq m$ has a subgraph $H$ with
$\delta(H)\geq k$.
-/
@[category research open, question, AMS 5]
theorem erdos_761.parts.ii :
    ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type*) [Finite V] (G : SimpleGraph V),
      (m : ℕ∞) ≤ G.cochromaticNumber →
        ∃ H : G.Subgraph, (k : ℕ∞) ≤ dichromaticNumber H.coe := by
  sorry

/--
A positive answer to the second question implies a positive answer to the first via the bound
mentioned in [760].
-/
@[category research solved, AMS 5]
theorem erdos_761.variants.parts_ii_imp_i :
    (∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (m : ℕ∞) ≤ G.cochromaticNumber →
        ∃ H : G.Subgraph, (k : ℕ∞) ≤ dichromaticNumber H.coe) →
    ∀ k : ℕ, ∃ m : ℕ, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ dichromaticNumber G := by
  sorry

end Erdos761
