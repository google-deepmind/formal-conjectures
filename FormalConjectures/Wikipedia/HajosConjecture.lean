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
# Hajós' conjecture (1961) — disproved

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Haj%C3%B3s_conjecture_(graph_theory))
* [Ha61] Hajós, G. (1961). "Über eine Konstruktion nicht n-färbbarer Graphen."
  *Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg Math.-Natur. Reihe* 10, pp. 116--117.
* [Di52] Dirac, G. A. (1952). "A property of 4-chromatic graphs and some remarks on critical
  graphs." *J. London Math. Soc.* 27, pp. 85--92.
* [Ca79] Catlin, P. A. (1979). "Hajós' graph-coloring conjecture: variations and
  counterexamples." *J. Combin. Theory Ser. B* 26, pp. 268--274.
* [EF81] Erdős, P. and Fajtlowicz, S. (1981). "On the conjecture of Hajós." *Combinatorica* 1,
  pp. 141--143.
* [Th05] Thomassen, C. (2005). "Some remarks on Hajós' conjecture." *J. Combin. Theory Ser. B*
  93, pp. 95--105.
-/

open SimpleGraph

namespace HajosConjecture

variable {V W : Type*}

/-- A **subdivision model** of `H` in `G`: an injective map `f` of the vertices of `H` to
*branch vertices* of `G`, together with, for each edge `w w'` of `H`, a path in `G` from
`f w` to `f w'` whose internal vertices avoid all branch vertices and are disjoint from the
internal vertices of the paths of all other edges. -/
structure IsSubdivisionModel (H : SimpleGraph W) (G : SimpleGraph V) (f : W → V)
    (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')) : Prop where
  injective : Function.Injective f
  isPath : ∀ w w' h, (P w w' h).IsPath
  internal_avoid : ∀ w w' h x, x ∈ (P w w' h).support.tail.dropLast → x ∉ Set.range f
  internal_disjoint : ∀ w₁ w₁' h₁ w₂ w₂' h₂, s(w₁, w₁') ≠ s(w₂, w₂') →
    ∀ x, x ∈ (P w₁ w₁' h₁).support.tail.dropLast → x ∉ (P w₂ w₂' h₂).support.tail.dropLast

/-- `G` contains a **subdivision** of `H` (i.e. `H` is a topological minor of `G`). -/
def ContainsSubdivision (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ (f : W → V) (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')), IsSubdivisionModel H G f P

/--
**Hajós' conjecture (1961) — disproved.**

Hajós conjectured that every graph with chromatic number at least $k$ contains a subdivision of
$K_k$ (a strengthening of Hadwiger's conjecture). This is **false**: Catlin [Ca79] gave
counterexamples for every $k \ge 7$, and Erdős and Fajtlowicz [EF81] showed that almost all
graphs are counterexamples.
-/
@[category research solved, AMS 5]
theorem hajos_conjecture : answer(False) ↔
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G := by
  sorry

/--
**The cases $k \le 4$ (Dirac 1952).**

Every graph with chromatic number at least $4$ contains a subdivision of $K_4$; the cases
$k \le 3$ are elementary.

*Reference:* [Di52].
-/
@[category research solved, AMS 5]
theorem hajos_conjecture.variants.le_four
    {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4)
    (h : (k : ℕ∞) ≤ G.chromaticNumber) : ContainsSubdivision (completeGraph (Fin k)) G := by
  sorry

/--
**The cases $k = 5$ and $k = 6$ remain open.**

Whether every $5$-chromatic graph contains a subdivision of $K_5$, and every $6$-chromatic graph
a subdivision of $K_6$, is unknown (see [Th05]).
-/
@[category research open, AMS 5]
theorem hajos_conjecture.variants.five_six : answer(sorry) ↔
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ), k = 5 ∨ k = 6 →
      (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G := by
  sorry

/--
**Catlin (1979): counterexamples for every $k \ge 7$.**

*Reference:* [Ca79].
-/
@[category research solved, AMS 5]
theorem hajos_conjecture.variants.catlin (k : ℕ) (hk : 7 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (k : ℕ∞) ≤ G.chromaticNumber ∧ ¬ ContainsSubdivision (completeGraph (Fin k)) G := by
  sorry

/-- The identity map with trivial paths is a subdivision model of `G` in itself. -/
@[category API, AMS 5]
lemma containsSubdivision_self (G : SimpleGraph V) : ContainsSubdivision G G := by
  refine ⟨id, fun u v h => Walk.cons h Walk.nil, ⟨Function.injective_id, fun u v h => ?_,
    fun u v h x hx => ?_, fun u₁ v₁ h₁ u₂ v₂ h₂ _ x hx => ?_⟩⟩
  · exact Walk.IsPath.cons Walk.IsPath.nil (by simpa using G.ne_of_adj h)
  · simp at hx
  · simp at hx

end HajosConjecture
