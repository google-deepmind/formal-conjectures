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
# Erdős Problem 1008

*References:*
- [erdosproblems.com/1008](https://www.erdosproblems.com/1008)
- [CFS14b] Conlon, D. and Fox, J. and Sudakov, B., *Large subgraphs without complete bipartite
  graphs*. arXiv:1401.6711 (2014).
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

@[expose] public section

open SimpleGraph

namespace Erdos1008

set_option linter.style.formal_proof_palomar false in
/--
Does every graph with $m$ edges contain a subgraph with $\gg m^{2/3}$ edges which contains
no $C_4$?

This problem was first solved in the affirmative by Conlon, Fox, and Sudakov [CFS14b]. A simple
proof is given by Hunter in the comments.
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1008.lean"]
theorem erdos_1008 :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (2 / 3 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/--
Originally asked by Bollobás and Erdős in 'a colloquium on graph theory at Tihany' with $m^{2/3}$
replaced by $m^{3/4}$. Folkman showed this is false with the counterexample $K_{n,n^2}$, which has
$n^3$ edges, and yet every subgraph with $>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, question, AMS 5]
theorem erdos_1008.variants.three_quarters :
    ¬ ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (3 / 4 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/-- Two distinct vertices $u, u'$ with two distinct common neighbours $w, w'$ span a $C_4$. -/
@[category API, AMS 5]
lemma cycleGraph_four_isContained {V : Type*} {H : SimpleGraph V} {u u' w w' : V}
    (hu : u ≠ u') (hw : w ≠ w') (h₁ : H.Adj u w) (h₂ : H.Adj u w') (h₃ : H.Adj u' w)
    (h₄ : H.Adj u' w') : cycleGraph 4 ⊑ H := by
  have := h₁.ne; have := h₂.ne; have := h₃.ne; have := h₄.ne
  refine ⟨⟨⟨![u, w, u', w'], fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
  · rw [cycleGraph_adj (n := 2)] at hab
    fin_cases a <;> fin_cases b <;> first | (exfalso; revert hab; decide) | simp_all [H.adj_comm]
  · fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

open Finset in
/--
Folkman's counterexample $K_{n,n^2}$, which has $n^3$ edges, and yet every subgraph with
$>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.folkman (n : ℕ) :
    ((completeBipartiteGraph (Fin n) (Fin (n ^ 2))).edgeSet.ncard = n ^ 3) ∧
      ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n ^ 2)),
        n ^ 2 + n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H := by
  classical
  refine ⟨?_, fun H hH hcard => ?_⟩
  · simp [Set.ncard_def, encard_edgeSet_completeBipartiteGraph, ENat.card_eq_coe_fintype_card]
    rw [← Nat.cast_pow, ENat.toNat_natCast]; ring
  by_contra hC
  have hB : H.IsBipartiteWith ↑(univ.map .inl : Finset (Fin n ⊕ Fin (n ^ 2)))
      ↑(univ.map .inr : Finset (Fin n ⊕ Fin (n ^ 2))) :=
    ⟨by simp [Set.disjoint_left], fun u v h => by
      have := hH h; rcases u with u | u <;> rcases v with v | v <;> simp_all⟩
  set P : Fin (n ^ 2) → Finset (Finset (Fin n ⊕ Fin (n ^ 2))) :=
    fun j => (H.neighborFinset (.inr j)).powersetCard 2
  have hdisj : (↑(univ : Finset (Fin (n ^ 2))) : Set _).PairwiseDisjoint P := by
    intro j _ j' _ hj
    refine disjoint_left.mpr fun s hs hs' => ?_
    obtain ⟨hs, h2⟩ := mem_powersetCard.mp hs
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
    obtain ⟨hs', -⟩ := mem_powersetCard.mp hs'
    simp only [insert_subset_iff, singleton_subset_iff, mem_neighborFinset] at hs hs'
    exact hC (cycleGraph_four_isContained hab (Sum.inr_injective.ne hj) hs.1.symm hs'.1.symm
      hs.2.symm hs'.2.symm)
  have hsub : univ.biUnion P ⊆ (univ.map ⟨.inl, Sum.inl_injective⟩).powersetCard 2 := by
    refine biUnion_subset.mpr fun j _ s hs => ?_
    obtain ⟨hs, h2⟩ := mem_powersetCard.mp hs
    refine mem_powersetCard.mpr ⟨fun u hu => ?_, h2⟩
    have := hH (H.adj_symm (mem_neighborFinset _ _ _ |>.mp (hs hu)))
    cases u <;> simp_all
  have h1 := card_le_card hsub
  rw [card_biUnion hdisj, card_powersetCard, card_map, card_univ, Fintype.card_fin] at h1
  have h2 : ∑ j, H.degree (.inr j) = H.edgeSet.ncard := by
    have := isBipartiteWith_sum_degrees_eq_card_edges' hB
    rwa [sum_map, ← Set.ncard_coe_finset, coe_edgeFinset] at this
  have h3 : ∀ d : ℕ, d ≤ 1 + d.choose 2 := fun d => by
    rcases d with _ | _ | d <;> simp [Nat.choose_succ_succ]; omega
  have h4 := sum_le_sum fun j (_ : j ∈ univ) => h3 (H.degree (.inr j))
  simp only [P, card_powersetCard, card_neighborFinset_eq_degree, sum_add_distrib] at h1 h4
  simp at h4
  omega

/--
In [Er71] Erdős revises the conjecture to $m^{2/3}$, and notes $\gg m^{1/2}$ is trivial.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.lower_bound :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (1 / 2 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

end Erdos1008
