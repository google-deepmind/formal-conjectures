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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture19

def K3 : SimpleGraph (Fin 3) := completeGraph (Fin 3)

lemma K3_b : b K3 = 2 := by
  rw [SimpleGraph.b, SimpleGraph.largestInducedBipartiteSubgraphSize]
  norm_cast
  apply le_antisymm
  · -- b K3 <= 2
    apply csSup_le
    · use 0
      use ∅
      simp
      dsimp [SimpleGraph.IsBipartite]
      apply SimpleGraph.colorable_of_isEmpty
    · rintro n ⟨s, hs⟩
      by_contra h_gt
      simp at h_gt
      have h_card : s.card = 3 := by
        have : s.card ≤ 3 := Finset.card_le_univ s
        linarith
      have h_univ : s = Finset.univ := Finset.eq_univ_of_card s h_card
      rw [h_univ] at hs
      have h_bip : K3.IsBipartite := by
        have h_iso : K3.induce (Set.univ : Set (Fin 3)) ≃g K3 := SimpleGraph.induceUnivIso K3
        rw [← Finset.coe_univ] at h_iso
        exact hs.1.of_embedding h_iso.symm.toEmbedding
      have h_not_bip : ¬ K3.IsBipartite := by
        dsimp [SimpleGraph.IsBipartite]
        rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
        simp [K3, completeGraph, SimpleGraph.chromaticNumber_top]
        norm_num
      contradiction
  · -- b K3 >= 2
    apply le_csSup
    · use 3
      rintro n ⟨s, hs⟩
      rw [← hs.2]
      exact Finset.card_le_univ s
    · use {0, 1}
      constructor
      · -- K3.induce {0, 1} is bipartite (it's K2)
        dsimp [SimpleGraph.IsBipartite]
        fconstructor
        refine SimpleGraph.Coloring.mk (fun x => if (x : Fin 3) = 0 then 0 else 1) ?_
        intro u v huv
        have huv_ne : u ≠ v := SimpleGraph.Adj.ne huv
        have u_mem : (u : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := u.property
        have v_mem : (v : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := v.property
        simp only [Finset.mem_insert, Finset.mem_singleton] at u_mem v_mem
        rcases u_mem with u_eq_0 | u_eq_1 <;> rcases v_mem with v_eq_0 | v_eq_1
        · -- u = 0, v = 0
          exfalso; apply huv_ne; ext; simp only [u_eq_0, v_eq_0]
        · -- u = 0, v = 1
          simp only [u_eq_0, v_eq_1, ↓reduceIte]
          exact zero_ne_one
        · -- u = 1, v = 0
          simp only [u_eq_1, v_eq_0, ↓reduceIte, one_ne_zero]
          exact zero_ne_one.symm
        · -- u = 1, v = 1
          exfalso; apply huv_ne; ext; simp only [u_eq_1, v_eq_1]
      · simp

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

lemma K3_indepNeighbors (v : Fin 3) : indepNeighbors K3 v = 1 := by
  unfold indepNeighbors
  have h_induced : K3.induce (K3.neighborSet v) = completeGraph (K3.neighborSet v) := by
    ext a b
    simp [K3, completeGraph]
    simp [Subtype.coe_ne_coe]
  dsimp [indepNeighborsCard]
  rw [h_induced]
  haveI : Nonempty (K3.neighborSet v) := by
    use v + 1
    simp [K3, completeGraph, SimpleGraph.neighborSet, SimpleGraph.top_adj]
  haveI : Fintype (K3.neighborSet v) := Set.Finite.fintype (Set.toFinite _)
  rw [indepNum_completeGraph]
  norm_cast

theorem K3_not_counterexample :
    FLOOR ((∑ v ∈ Finset.univ, ecc K3 {v}) / (Fintype.card (Fin 3) : ℝ) + sSup (Set.range (fun (v : Fin 3) => indepNeighbors K3 v)))
      ≤ b K3 := by
  rw [K3_b]
  have h_ecc : ∀ v, ecc K3 {v} = 1 := K3_ecc
  simp [h_ecc]
  have h_indep : ∀ v, indepNeighbors K3 v = 1 := K3_indepNeighbors
  simp [h_indep]
  rw [FLOOR]
  norm_num
