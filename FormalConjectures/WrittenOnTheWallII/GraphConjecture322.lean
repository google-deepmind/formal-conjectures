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
# Written on the Wall II - Conjecture 322

*Reference:*
[E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.uhd.edu/faculty/delavinae/research/wowII/)

The source applies the local-independence hypothesis to the complement graph. Its conclusion
also follows from the characterization of minimal total dominating sets of complete multipartite
graphs in [M. Subramanian and A. Selvakumar, *Total Domination and Minimal Total Domination
Polynomial of H-Join Graphs*](https://doi.org/10.2298/FIL2501267S).
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture322

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 322](http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)

Let `G` be a simple connected graph on `n ≥ 5` vertices. If the maximum over all
vertices `v` of `l(v)` in the complement graph `Gᶜ` — the independence number of
the neighborhood `N(v)` of `v` — is at most 1, then `G` is well totally dominated.

Here `l(v) = α(Gᶜ[N(v)])` is the independence number of the subgraph induced by the
open neighborhood of `v` in `Gᶜ`.
-/
@[category research solved, AMS 5]
theorem conjecture322 (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected)
    (hn : 5 ≤ Fintype.card α)
    (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    IsWellTotallyDominated G := by
  have adj_of_local_independence_one (H : SimpleGraph α) {v x y : α}
      (hv : indepNeighborsCard H v ≤ 1) (hx : H.Adj v x) (hy : H.Adj v y)
      (hxy : x ≠ y) : H.Adj x y := by
    by_contra hnxy
    let x' : H.neighborSet v := ⟨x, hx⟩
    let y' : H.neighborSet v := ⟨y, hy⟩
    have hne : x' ≠ y' := by
      intro heq
      exact hxy (congrArg Subtype.val heq)
    have hind : (H.induce (H.neighborSet v)).IsIndepSet ({x', y'} : Finset _) := by
      rw [isIndepSet_iff]
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl)
      · exact (hab rfl).elim
      · exact hnxy
      · exact fun hyx ↦ hnxy hyx.symm
      · exact (hab rfl).elim
    have hle := hind.card_le_indepNum
    have hcard : ({x', y'} : Finset _).card = 2 := by simp [hne]
    rw [hcard] at hle
    exact (by omega : ¬(2 ≤ indepNeighborsCard H v)) hle
  have edge_total {x y : α} (hxy : G.Adj x y) : IsTotalDominatingSet G {x, y} := by
    intro v
    by_cases hvx : G.Adj v x
    · exact ⟨x, by simp, hvx⟩
    by_cases hvy : G.Adj v y
    · exact ⟨y, by simp, hvy⟩
    exfalso
    have hvx_ne : v ≠ x := by
      rintro rfl
      exact hvy hxy
    have hvy_ne : v ≠ y := by
      rintro rfl
      exact hvx hxy.symm
    have hvx_compl : Gᶜ.Adj v x := (G.compl_adj v x).2 ⟨hvx_ne, hvx⟩
    have hvy_compl : Gᶜ.Adj v y := (G.compl_adj v y).2 ⟨hvy_ne, hvy⟩
    have hxy_compl : Gᶜ.Adj x y :=
      adj_of_local_independence_one Gᶜ (h v) hvx_compl hvy_compl hxy.ne
    exact ((G.compl_adj x y).1 hxy_compl).2 hxy
  have minimal_card_two {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
      S.card = 2 := by
    have hcardpos : 0 < Fintype.card α := by omega
    let v : α := Classical.choice (Fintype.card_pos_iff.mp hcardpos)
    obtain ⟨w, hwS, _⟩ := hS.1 v
    obtain ⟨x, hxS, hwx⟩ := hS.1 w
    have hpair_subset : ({w, x} : Finset α) ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        (And.intro hwS hxS)
    have hpair_not_ssubset : ¬({w, x} : Finset α) ⊂ S := by
      intro hss
      exact hS.2 {w, x} hss (edge_total hwx)
    have hpair_eq : ({w, x} : Finset α) = S :=
      hpair_subset.eq_of_not_ssubset hpair_not_ssubset
    rw [← hpair_eq]
    simp [hwx.ne]
  intro S T hS hT
  rw [minimal_card_two hS, minimal_card_two hT]

-- Sanity checks

/-- In `K₄`, all vertices have degree 3. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 4)).maxDegree = 3 := by decide +native

/-- In the edgeless graph `⊥` on 5 vertices, the minimum degree is 0. -/
@[category test, AMS 5]
example : (⊥ : SimpleGraph (Fin 5)).minDegree = 0 := by decide +native

end WrittenOnTheWallII.GraphConjecture322
