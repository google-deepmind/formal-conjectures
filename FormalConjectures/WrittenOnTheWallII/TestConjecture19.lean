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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture19
import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 19: verification for `K₃`

This file verifies WOWII Conjecture 19 on the concrete graph `K₃`
(the complete graph on three vertices), computing both sides of the
conjectured inequality explicitly.
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture19

def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)

@[category test, AMS 5]
lemma K3_b : b K3 = 2 := by
  simp only [GraphConjecture19.K3, b]
  norm_cast
  refine IsGreatest.csSup_eq ?_
  constructor
  · simp [SimpleGraph.IsBipartite]
    use {0,1}
    constructor
    · use fun i => ite (i.1 = 0) 0 1
      simp
      decide
    · decide
  · simp only [upperBounds, Finset.coe_sort_coe, completeGraph_eq_top, Set.mem_setOf_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    cases ha
    cases ‹_›
    decide+revert   

@[category test, AMS 5]
lemma K3_ecc (v : Fin 3) : ecc K3 {v} = 1 := by
  unfold ecc
  have h_dist : ∀ w, w ≠ v → distToSet K3 w {v} = 1 := by
    intro w hw
    simp [distToSet, K3, completeGraph, SimpleGraph.dist_eq_one_iff_adj, SimpleGraph.top_adj]
    exact hw
  have h_image : (Finset.univ.filter (fun x => x ≠ v)).image (fun x => distToSet K3 x {v}) = {1} := by
    ext x
    constructor
    · intro h
      rw [Finset.mem_image] at h
      rcases h with ⟨w, hw1, hw2⟩
      rw [h_dist w] at hw2
      · rw [← hw2]
        simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1
        exact hw1
    · intro h
      simp at h
      rw [h]
      rw [Finset.mem_image]
      use (v + 1)
      constructor
      · simp
      · rw [h_dist]
        simp
  -- We need to show the condition is true
  have h_nonempty : (Finset.univ.filter (fun x => x ∉ ({v} : Set (Fin 3)))).Nonempty := by
    use (v + 1)
    simp
  dsimp
  split_ifs with h_cond
  · convert Finset.max'_singleton 1
    simp [h_image]
  · exact h_cond (by convert h_nonempty)

@[category test, AMS 5]
lemma indepNum_completeGraph {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] :
    (completeGraph V).indepNum = 1 := by
  rw [SimpleGraph.indepNum, completeGraph_eq_top]
  apply le_antisymm
  · apply csSup_le
    · use 1
      use {Classical.arbitrary V}
      simp [SimpleGraph.isNIndepSet_iff]
    · rintro n ⟨s, hs⟩
      rw [SimpleGraph.isNIndepSet_iff] at hs
      obtain ⟨h_indep, h_card⟩ := hs
      rw [SimpleGraph.isIndepSet_iff] at h_indep
      have h_sub : (s : Set V).Subsingleton := by
        intro a ha b hb
        by_contra h_ne
        have h_adj : ¬ (⊤ : SimpleGraph V).Adj a b := h_indep ha hb h_ne
        simp [SimpleGraph.top_adj] at h_adj
        contradiction
      rw [← h_card]
      exact Finset.card_le_one.mpr h_sub
  · apply le_csSup
    · use Fintype.card V
      rintro n ⟨s, hs⟩
      rw [← hs.card_eq]
      exact Finset.card_le_univ s
    · use {Classical.arbitrary V}
      simp [SimpleGraph.isNIndepSet_iff]

@[category test, AMS 5]
lemma K3_indepNeighbors (v : Fin 3) : indepNeighbors K3 v = 1 := by
  unfold indepNeighbors
  have h_induced : K3.induce (K3.neighborSet v) = completeGraph (K3.neighborSet v) := by
    ext a b
    show (a : Fin 3) ≠ b ↔ a ≠ b
    exact Subtype.val_injective.ne_iff
  dsimp [indepNeighborsCard]
  rw [h_induced]
  have : Nonempty (K3.neighborSet v) := by
    use v + 1
    simp [K3, completeGraph, SimpleGraph.neighborSet, SimpleGraph.top_adj]
  have : Fintype (K3.neighborSet v) := Set.Finite.fintype (Set.toFinite _)
  rw [indepNum_completeGraph]
  norm_cast

@[category test, AMS 5]
theorem K3_not_counterexample :
    ⌊(∑ v ∈ Finset.univ, ((K3.eccent v).toNat : ℝ)) / (Fintype.card (Fin 3) : ℝ) +
      sSup (Set.range (indepNeighbors K3))⌋ ≤ b K3 := by
  have h_ecc : ∀ v : Fin 3, K3.eccent v = 1 := fun v => by
    rw [K3, completeGraph_eq_top]
    exact SimpleGraph.eccent_top v
  have h_range : Set.range (indepNeighbors K3) = {1} := by
    ext x
    simp [K3_indepNeighbors, eq_comm]
  rw [K3_b, h_range]
  simp [h_ecc]
