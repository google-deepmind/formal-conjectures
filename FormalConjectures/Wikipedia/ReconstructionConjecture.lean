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

import FormalConjecturesUtil

/-!
# The reconstruction conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Reconstruction_conjecture)
* [Ke57] Kelly, P. J. (1957). "A congruence theorem for trees." *Pacific J. Math.* 7,
  pp. 961--968.
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, New York.
* [Ha64] Harary, F. (1964). "On the reconstruction of a graph from a collection of subgraphs."
  In *Theory of Graphs and its Applications*, Academia, Prague, pp. 47--52.
* [Lo72] Lovász, L. (1972). "A note on the line reconstruction problem." *J. Combin. Theory
  Ser. B* 13, pp. 309--310.
* [Mu77] Müller, V. (1977). "The edge reconstruction hypothesis is true for graphs with more
  than n·log n edges." *J. Combin. Theory Ser. B* 22, pp. 281--283.
* [Bo91] Bondy, J. A. (1991). "A graph reconstructor's manual." In *Surveys in Combinatorics*,
  LMS Lecture Note Series 166, Cambridge University Press, pp. 221--252.
-/

namespace ReconstructionConjecture

variable {V W : Type*}

/-- Two graphs are **hypomorphic** if there is a bijection `σ` between their vertex sets such
that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for every vertex `v`;
i.e. `G` and `H` have the same deck of vertex-deleted subgraphs. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

/-- Isomorphic graphs are hypomorphic: an isomorphism restricts to an isomorphism between
corresponding vertex-deleted subgraphs. -/
@[category API, AMS 5]
lemma Hypomorphic.of_iso {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    Hypomorphic G H := by
  refine ⟨f.toEquiv, fun v => ⟨⟨Equiv.subtypeEquiv f.toEquiv fun x => ?_, ?_⟩⟩⟩
  · simp
  · intro a b
    exact f.map_rel_iff

/-- Hypomorphic graphs have the same number of vertices. -/
@[category API, AMS 5]
lemma Hypomorphic.card_eq [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Fintype.card V = Fintype.card W := by
  obtain ⟨σ, -⟩ := h
  exact Fintype.card_congr σ

/-- Any two graphs on subsingleton vertex types are isomorphic. -/
@[category API, AMS 5]
lemma nonempty_iso_of_subsingleton [Subsingleton V] [Subsingleton W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ≃ W) : Nonempty (G ≃g H) := by
  refine ⟨⟨e, ?_⟩⟩
  intro a b
  cases Subsingleton.elim a b
  exact iff_of_false (H.irrefl) (G.irrefl)

/--
**The reconstruction conjecture** (Kelly [Ke57], Ulam [Ul60]).

Every finite simple graph on at least three vertices is determined up to isomorphism by its
deck of vertex-deleted subgraphs: any two hypomorphic graphs on at least three vertices are
isomorphic.
-/
@[category research open, AMS 5]
theorem reconstruction_conjecture {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Trees are reconstructible** (Kelly [Ke57]).

Every tree on at least three vertices is determined up to isomorphism by its deck of
vertex-deleted subgraphs.
-/
@[category research solved, AMS 5]
theorem reconstruction_conjecture.variants.tree {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hc : G.Connected) (ha : G.IsAcyclic) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Disconnected graphs are reconstructible.**

Every disconnected graph on at least three vertices is determined up to isomorphism by its
deck of vertex-deleted subgraphs; see [Bo91].
-/
@[category research solved, AMS 5]
theorem reconstruction_conjecture.variants.disconnected {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hd : ¬G.Connected) (h : Hypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**The hypothesis of three vertices is necessary.**

The two graphs on two vertices — the single edge and its complement — are hypomorphic (both
decks consist of two one-vertex graphs) but not isomorphic.
-/
@[category test, AMS 5]
theorem reconstruction_conjecture.variants.two_vertices :
    Hypomorphic (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) ∧
      IsEmpty ((⊤ : SimpleGraph (Fin 2)) ≃g (⊥ : SimpleGraph (Fin 2))) := by
  constructor
  · have hss : ∀ v : Fin 2, Subsingleton (({v}ᶜ : Set (Fin 2)) : Type) := by
      intro v
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      apply Subtype.ext
      fin_cases v <;> fin_cases a <;> fin_cases b <;> simp_all
    refine ⟨Equiv.refl (Fin 2), fun v => ?_⟩
    have := hss v
    exact nonempty_iso_of_subsingleton _ _ (Equiv.refl _)
  · exact ⟨fun f => ((f.map_rel_iff (a := 0) (b := 1)).mpr Fin.zero_ne_one : False)⟩

/--
**The edge reconstruction conjecture** (Harary [Ha64]).

Every finite simple graph with at least four edges is determined up to isomorphism by its
deck of edge-deleted subgraphs: any two edge-hypomorphic graphs on the same vertex set with
at least four edges are isomorphic.
-/
@[category research open, AMS 5]
theorem edge_reconstruction_conjecture {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hE : 4 ≤ G.edgeSet.ncard) (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Lovász (1972): graphs with more than half of all possible edges are edge-reconstructible.**

If a graph on `n` vertices has more than `n (n - 1) / 4` edges, then it is determined up to
isomorphism by its deck of edge-deleted subgraphs.

*Reference:* [Lo72].
-/
@[category research solved, AMS 5]
theorem edge_reconstruction_conjecture.variants.lovasz {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : (Fintype.card V).choose 2 < 2 * G.edgeSet.ncard)
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/--
**Müller (1977): graphs with many edges are edge-reconstructible.**

If a graph on `n` vertices with `m` edges satisfies `n! < 2 ^ (m - 1)`, then it is determined
up to isomorphism by its deck of edge-deleted subgraphs.

*Reference:* [Mu77].
-/
@[category research solved, AMS 5]
theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

end ReconstructionConjecture
