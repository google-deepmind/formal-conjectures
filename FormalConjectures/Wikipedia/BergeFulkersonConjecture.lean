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
# The Berge–Fulkerson conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [Fu71] Fulkerson, D. R. (1971). "Blocking and anti-blocking pairs of polyhedra."
  *Math. Programming* 1, pp. 168--194.
* [Se79] Seymour, P. D. (1979). "On multi-colourings of cubic graphs, and conjectures of
  Fulkerson and Tutte." *Proc. London Math. Soc.* 38, pp. 423--460.
* [Ma11] Mazzuoccolo, G. (2011). "The equivalence of two conjectures of Berge and Fulkerson."
  *J. Graph Theory* 68, pp. 125--128.
* [FR94] Fan, G. and Raspaud, A. (1994). "Fulkerson's conjecture and circuit covers."
  *J. Combin. Theory Ser. B* 61, pp. 133--138.
* [Pe91] Petersen, J. (1891). "Die Theorie der regulären graphs." *Acta Math.* 15,
  pp. 193--220.
-/

open SimpleGraph Finset

namespace BergeFulkersonConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **cubic** if every vertex has degree `3`. -/
def IsCubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3

open Classical in
/-- A family of `k` perfect matchings of `G` **covers every edge exactly `m` times** if each
member is a perfect matching and every edge of `G` lies in exactly `m` of them. -/
def IsPerfectMatchingCover (G : SimpleGraph V) (k m : ℕ) (M : Fin k → G.Subgraph) : Prop :=
  (∀ i, (M i).IsPerfectMatching) ∧
    ∀ e ∈ G.edgeSet, (univ.filter fun i => e ∈ (M i).edgeSet).card = m

/--
**The Berge–Fulkerson conjecture (Fulkerson 1971).**

Every bridgeless cubic graph has six perfect matchings such that every edge lies in exactly two
of them.
-/
@[category research open, AMS 5]
theorem berge_fulkerson_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → G.IsBridgeless →
      ∃ M : Fin 6 → G.Subgraph, IsPerfectMatchingCover G 6 2 M := by
  sorry

/--
**Berge's conjecture: five perfect matchings covering every edge.**

Every bridgeless cubic graph has five perfect matchings whose union is the whole edge set.
Mazzuoccolo [Ma11] proved this to be equivalent to the Berge–Fulkerson conjecture.

*Reference:* [Ma11].
-/
@[category research open, AMS 5]
theorem berge_fulkerson_conjecture.variants.berge :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → G.IsBridgeless →
      ∃ M : Fin 5 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet := by
  sorry

/--
**The Fan–Raspaud conjecture (1994).**

Every bridgeless cubic graph has three perfect matchings with no edge common to all three.
This would follow from the Berge–Fulkerson conjecture.

*Reference:* [FR94].
-/
@[category research open, AMS 5]
theorem berge_fulkerson_conjecture.variants.fan_raspaud :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCubic G → G.IsBridgeless →
      ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
        ∀ e, ¬ (e ∈ (M 0).edgeSet ∧ e ∈ (M 1).edgeSet ∧ e ∈ (M 2).edgeSet) := by
  sorry

/--
**Petersen's theorem (1891): every bridgeless cubic graph has a perfect matching.**

This is the case of a single perfect matching, and is the starting point for all of the
above.

*Reference:* [Pe91].
-/
@[category research solved, AMS 5]
theorem berge_fulkerson_conjecture.variants.petersen
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : IsCubic G) (hbridgeless : G.IsBridgeless) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

open Classical in
omit [Fintype V] [DecidableEq V] in
/-- Any perfect-matching cover of `G` by `k` matchings covering each edge `m` times satisfies
`k ≥ m` as soon as `G` has an edge. -/
@[category API, AMS 5]
lemma le_of_isPerfectMatchingCover {G : SimpleGraph V} {k m : ℕ} {M : Fin k → G.Subgraph}
    (hM : IsPerfectMatchingCover G k m M) {e : Sym2 V} (he : e ∈ G.edgeSet) : m ≤ k :=
  calc m = (univ.filter fun i => e ∈ (M i).edgeSet).card := (hM.2 e he).symm
    _ ≤ (univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := Finset.card_fin k

end BergeFulkersonConjecture
