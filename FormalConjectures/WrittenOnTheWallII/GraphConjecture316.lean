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
# Written on the Wall II - Conjecture 316

*Reference:*
[E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.uhd.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

@[category API, AMS 5]
private lemma edge_count_le_pendant_add_induce (G : SimpleGraph α) [DecidableRel G.Adj]
    (P Q : Finset α) (hQ : Q = Finset.univ \ P)
    (hP : ∀ v ∈ P, G.degree v = 1) :
    G.edgeFinset.card ≤ P.card + (G.edgeFinset ∩ Q.sym2).card := by
  let I : Finset (Sym2 α) := P.biUnion fun v => G.incidenceFinset v
  have hcover : G.edgeFinset ⊆ (G.edgeFinset ∩ Q.sym2) ∪ I := by
    intro e he
    by_cases heQ : e ∈ Q.sym2
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨he, heQ⟩)
    · induction e using Sym2.inductionOn with | _ a b =>
      simp only [Finset.mk_mem_sym2_iff] at heQ
      rw [Finset.mem_union]
      right
      rw [Finset.mem_biUnion]
      rw [SimpleGraph.mem_edgeFinset] at he
      rw [SimpleGraph.mem_edgeSet] at he
      rcases not_and_or.mp heQ with ha | hb
      · have haP : a ∈ P := by simpa [hQ] using ha
        refine ⟨a, haP, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
        exact ⟨he, Or.inl rfl⟩
      · have hbP : b ∈ P := by simpa [hQ] using hb
        refine ⟨b, hbP, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
        exact ⟨he, Or.inr rfl⟩
  have hI : I.card ≤ P.card := by
    calc
      I.card ≤ ∑ v ∈ P, (G.incidenceFinset v).card := Finset.card_biUnion_le
      _ = ∑ _v ∈ P, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [hP v hv]
      _ = P.card := by simp
  calc
    G.edgeFinset.card ≤ ((G.edgeFinset ∩ Q.sym2) ∪ I).card := Finset.card_le_card hcover
    _ ≤ (G.edgeFinset ∩ Q.sym2).card + I.card :=
      Finset.card_union_le (G.edgeFinset ∩ Q.sym2) I
    _ ≤ (G.edgeFinset ∩ Q.sym2).card + P.card := by omega
    _ = P.card + (G.edgeFinset ∩ Q.sym2).card := Nat.add_comm _ _

@[category API, AMS 5]
private lemma induce_edge_count_le_choose (G : SimpleGraph α) [DecidableRel G.Adj]
    (Q : Finset α) :
    (G.edgeFinset ∩ Q.sym2).card ≤ Q.card.choose 2 := by
  letI : Fintype (Q : Set α) := Subtype.fintype (Membership.mem (Q : Set α))
  have hm := congrArg Finset.card
    (SimpleGraph.map_edgeFinset_induce (G := G) (s := (Q : Set α)))
  have hb := SimpleGraph.card_edgeFinset_le_card_choose_two
    (G := G.induce (Q : Set α))
  have hq : Fintype.card (Q : Set α) = Q.card := by simp
  rw [hq] at hb
  have hm' : (G.induce (Q : Set α)).edgeFinset.card =
      (G.edgeFinset ∩ Q.sym2).card := by simpa using hm
  rw [← hm']
  exact hb

@[category API, AMS 5]
private lemma average_compl_edge_bound [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (P : Finset α)
    (h : (averageDegree Gᶜ : ℚ) ≤ P.card) :
    2 * Gᶜ.edgeFinset.card ≤ P.card * Fintype.card α := by
  have hn : (0 : ℚ) < Fintype.card α := by positivity
  unfold averageDegree at h
  rw [div_le_iff₀ hn] at h
  rw [← Nat.cast_sum] at h
  rw [Gᶜ.sum_degrees_eq_twice_card_edges] at h
  exact_mod_cast h

@[category API, AMS 5]
private lemma edge_count_add_compl (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card α).choose 2 := by
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.2 disjoint_compl_right
  rw [← SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  rw [← Finset.card_union_of_disjoint hd]
  rw [← SimpleGraph.edgeFinset_sup]
  exact congrArg Finset.card (SimpleGraph.edgeFinset_inj.2 sup_compl_eq_top)

omit [DecidableEq α] in
@[category API, AMS 5]
private lemma connected_edge_lower (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) : Fintype.card α ≤ G.edgeFinset.card + 1 := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have hcard : T.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
  have hle : T.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hTG)
  omega

@[category API, AMS 5]
private lemma nonpendant_card_le_three [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (P Q : Finset α) (hQ : Q = Finset.univ \ P)
    (hp : 0 < P.card) (hP : ∀ v ∈ P, G.degree v = 1)
    (h : (averageDegree Gᶜ : ℚ) ≤ P.card) : Q.card ≤ 3 := by
  have hpartition : P.card + Q.card = Fintype.card α := by
    rw [hQ, Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    rw [Finset.card_univ]
    have hp_le : P.card ≤ Fintype.card α := by
      simpa using Finset.card_le_card (Finset.subset_univ P)
    omega
  have hcomp := average_compl_edge_bound G P h
  have htotal := edge_count_add_compl G
  have hedge := edge_count_le_pendant_add_induce G P Q hQ hP
  have hcore := induce_edge_count_le_choose G Q
  have hupper : G.edgeFinset.card ≤ P.card + Q.card.choose 2 := by omega
  have hcompQ : (2 : ℚ) * Gᶜ.edgeFinset.card ≤
      (P.card : ℚ) * Fintype.card α := by exact_mod_cast hcomp
  have htotalQ : (G.edgeFinset.card : ℚ) + Gᶜ.edgeFinset.card =
      ((Fintype.card α).choose 2 : ℚ) := by exact_mod_cast htotal
  rw [Nat.cast_choose_two] at htotalQ
  have hupperQ : (G.edgeFinset.card : ℚ) ≤
      P.card + (Q.card.choose 2 : ℚ) := by exact_mod_cast hupper
  rw [Nat.cast_choose_two] at hupperQ
  have hpartitionQ : (P.card : ℚ) + Q.card = Fintype.card α := by
    exact_mod_cast hpartition
  have hpQ : (0 : ℚ) < P.card := by exact_mod_cast hp
  by_contra hnq
  have hqNat : 4 ≤ Q.card := by omega
  have hqQ : (4 : ℚ) ≤ Q.card := by exact_mod_cast hqNat
  nlinarith

@[category API, AMS 5]
private lemma eq_top_of_card_edgeFinset_eq_choose (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hcard : G.edgeFinset.card = (Fintype.card α).choose 2) : G = ⊤ := by
  rw [← SimpleGraph.edgeFinset_inj]
  apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcard]

omit [Fintype α] in
@[category API, AMS 5]
private lemma wellTotallyDominated_of_eq_top [Nonempty α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G = ⊤) : IsWellTotallyDominated G := by
  have edge_total {x y : α} (hxy : G.Adj x y) : IsTotalDominatingSet G {x, y} := by
    intro v
    by_cases hvx : v = x
    · exact ⟨y, by simp, hvx ▸ hxy⟩
    · exact ⟨x, by simp, by simpa [hG]⟩
  have minimal_card_two {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
      S.card = 2 := by
    let v : α := Classical.choice ‹Nonempty α›
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

@[category API, AMS 5]
private lemma card_le_two_of_adjacent_degree_one (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G.Connected) {u v : α} (hu : G.degree u = 1)
    (hv : G.degree v = 1) (huv : G.Adj u v) : Fintype.card α ≤ 2 := by
  have hu_unique : ∀ w, G.Adj u w → w = v := by
    intro w huw
    exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu).unique huw huv
  have hv_unique : ∀ w, G.Adj v w → w = u := by
    intro w hvw
    exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv).unique hvw huv.symm
  have hall : (Finset.univ : Finset α) ⊆ {u, v} := by
    intro w _hw
    obtain ⟨p, hp⟩ := hG.exists_isPath u w
    cases p with
    | nil => simp
    | @cons _ x _ hux p =>
      have hx : x = v := hu_unique x hux
      subst x
      cases p with
      | nil => simp
      | @cons _ x _ hvx p =>
        have hx : x = u := hv_unique x hvx
        subst x
        simp [SimpleGraph.Walk.cons_isPath_iff] at hp
  calc
    Fintype.card α = (Finset.univ : Finset α).card := by simp
    _ ≤ ({u, v} : Finset α).card := Finset.card_le_card hall
    _ ≤ 2 := Finset.card_le_two

@[category API, AMS 5]
private lemma isClique_of_induce_edge_count_eq_choose (G : SimpleGraph α)
    [DecidableRel G.Adj] (Q : Finset α)
    (hcard : (G.edgeFinset ∩ Q.sym2).card = Q.card.choose 2) :
    G.IsClique (Q : Set α) := by
  rw [SimpleGraph.isClique_iff_induce_eq]
  letI : Fintype (Q : Set α) := Subtype.fintype (Membership.mem (Q : Set α))
  apply eq_top_of_card_edgeFinset_eq_choose
  have hm := congrArg Finset.card
    (SimpleGraph.map_edgeFinset_induce (G := G) (s := (Q : Set α)))
  have hm' : (G.induce (Q : Set α)).edgeFinset.card =
      (G.edgeFinset ∩ Q.sym2).card := by simpa using hm
  rw [hm', hcard]
  congr 1
  simp

@[category API, AMS 5]
private lemma nonpendant_isClique [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G.Connected) (P Q : Finset α)
    (hQ : Q = Finset.univ \ P) (hn : 3 ≤ Fintype.card α) (hp : 0 < P.card)
    (hP : ∀ v ∈ P, G.degree v = 1)
    (h : (averageDegree Gᶜ : ℚ) ≤ P.card) : G.IsClique (Q : Set α) := by
  have hpartition : P.card + Q.card = Fintype.card α := by
    rw [hQ, Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ]
    have hp_le : P.card ≤ Fintype.card α := by
      simpa using Finset.card_le_card (Finset.subset_univ P)
    omega
  have hq_le : Q.card ≤ 3 := nonpendant_card_le_three G P Q hQ hp hP h
  have hq_pos : 0 < Q.card := by
    obtain ⟨v, hvP⟩ := Finset.card_pos.mp hp
    obtain ⟨w, hvw⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (hP v hvP)).exists
    have hwQ : w ∈ Q := by
      rw [hQ]
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hwP
      have hcard := card_le_two_of_adjacent_degree_one G hG (hP v hvP) (hP w hwP) hvw
      omega
    exact Finset.card_pos.mpr ⟨w, hwQ⟩
  have hedge := edge_count_le_pendant_add_induce G P Q hQ hP
  have hcore := induce_edge_count_le_choose G Q
  have hcases : Q.card = 1 ∨ Q.card = 2 ∨ Q.card = 3 := by omega
  rcases hcases with hq | hq | hq
  · apply isClique_of_induce_edge_count_eq_choose G Q
    norm_num [hq] at hcore ⊢
    exact hcore
  · have hlower := connected_edge_lower G hG
    apply isClique_of_induce_edge_count_eq_choose G Q
    norm_num [hq] at hcore ⊢
    omega
  · have hcomp := average_compl_edge_bound G P h
    have htotal := edge_count_add_compl G
    have hcompQ : (2 : ℚ) * Gᶜ.edgeFinset.card ≤
        (P.card : ℚ) * Fintype.card α := by exact_mod_cast hcomp
    have htotalQ : (G.edgeFinset.card : ℚ) + Gᶜ.edgeFinset.card =
        ((Fintype.card α).choose 2 : ℚ) := by exact_mod_cast htotal
    rw [Nat.cast_choose_two] at htotalQ
    have hpartitionQ : (P.card : ℚ) + Q.card = Fintype.card α := by
      exact_mod_cast hpartition
    have hqQ : (Q.card : ℚ) = 3 := by exact_mod_cast hq
    have hmQ : (P.card : ℚ) + 3 ≤ G.edgeFinset.card := by nlinarith
    have hm : P.card + 3 ≤ G.edgeFinset.card := by exact_mod_cast hmQ
    apply isClique_of_induce_edge_count_eq_choose G Q
    norm_num [hq] at hcore ⊢
    omega

@[category API, AMS 5]
private lemma wellTotallyDominated_of_pendant_core_clique (G : SimpleGraph α)
    [DecidableRel G.Adj] (P Q : Finset α) (hQ : Q = Finset.univ \ P)
    (hp : 0 < P.card) (hP : ∀ v ∈ P, G.degree v = 1)
    (hleaf : ∀ v ∈ P, ∀ w, G.Adj v w → w ∈ Q)
    (hclique : G.IsClique (Q : Set α)) : IsWellTotallyDominated G := by
  let A : Finset α := Q.filter fun a => ∃ v ∈ P, G.Adj v a
  have leaf_has_support (v : α) (hvP : v ∈ P) : ∃ a ∈ A, G.Adj v a := by
    obtain ⟨a, hva⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (hP v hvP)).exists
    refine ⟨a, ?_, hva⟩
    simp only [A, Finset.mem_filter]
    exact ⟨hleaf v hvP a hva, ⟨v, hvP, hva⟩⟩
  have hA_nonempty : A.Nonempty := by
    obtain ⟨v, hvP⟩ := Finset.card_pos.mp hp
    obtain ⟨a, haA, _⟩ := leaf_has_support v hvP
    exact ⟨a, haA⟩
  have hA_subset_Q : A ⊆ Q := by
    intro a ha
    simp only [A, Finset.mem_filter] at ha
    exact ha.1
  have support_subset {S : Finset α} (hS : IsTotalDominatingSet G S) : A ⊆ S := by
    intro a haA
    obtain ⟨haQ, v, hvP, hva⟩ : a ∈ Q ∧ ∃ v ∈ P, G.Adj v a := by simpa [A] using haA
    obtain ⟨w, hwS, hvw⟩ := hS v
    have hwa : w = a :=
      (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (hP v hvP)).unique hvw hva
    simpa [hwa] using hwS
  by_cases hA_two : 2 ≤ A.card
  · have hA_total : IsTotalDominatingSet G A := by
      intro v
      by_cases hvP : v ∈ P
      · obtain ⟨a, haA, hva⟩ := leaf_has_support v hvP
        exact ⟨a, haA, hva⟩
      · have hvQ : v ∈ Q := by simp [hQ, hvP]
        obtain ⟨a, haA, hav⟩ := A.exists_mem_ne (by omega) v
        have haQ := hA_subset_Q haA
        exact ⟨a, haA, hclique hvQ haQ hav.symm⟩
    have minimal_eq_support {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
        S = A := by
      have hAS : A ⊆ S := support_subset hS.1
      apply Finset.Subset.antisymm ?_ hAS
      by_contra hnot
      have hne : A ≠ S := by
        intro heq
        apply hnot
        simp [heq]
      have hproper : A ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hne⟩
      exact hS.2 A hproper hA_total
    intro S T hS hT
    rw [minimal_eq_support hS, minimal_eq_support hT]
  · have hA_card : A.card = 1 := by
      have hpos : 0 < A.card := Finset.card_pos.mpr hA_nonempty
      omega
    obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hA_card
    have minimal_card_two {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
        S.card = 2 := by
      have haS : a ∈ S := by
        have haA : a ∈ A := by simp [hA]
        exact support_subset hS.1 haA
      obtain ⟨x, hxS, hax⟩ := hS.1 a
      have hpair_subset : ({a, x} : Finset α) ⊆ S := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          (And.intro haS hxS)
      have hpair_total : IsTotalDominatingSet G {a, x} := by
        intro v
        by_cases hvP : v ∈ P
        · obtain ⟨b, hbA, hvb⟩ := leaf_has_support v hvP
          have hba : b = a := by simpa [hA] using hbA
          exact ⟨a, by simp, hba ▸ hvb⟩
        · have hvQ : v ∈ Q := by simp [hQ, hvP]
          by_cases hva : v = a
          · exact ⟨x, by simp, hva ▸ hax⟩
          · have haQ : a ∈ Q := hA_subset_Q (by simp [hA])
            exact ⟨a, by simp, hclique hvQ haQ hva⟩
      have hpair_not_ssubset : ¬({a, x} : Finset α) ⊂ S := by
        intro hss
        exact hS.2 {a, x} hss hpair_total
      have hpair_eq : ({a, x} : Finset α) = S :=
        hpair_subset.eq_of_not_ssubset hpair_not_ssubset
      rw [← hpair_eq]
      simp [hax.ne]
    intro S T hS hT
    rw [minimal_card_two hS, minimal_card_two hT]

/--
WOWII [Conjecture 316](http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)

Let `G` be a simple connected graph and let `P` denote the set of pendant vertices
(vertices of degree 1). If `|P| ≥ deg_avg(Gᶜ)`, then `G` is well totally dominated,
where `deg_avg(Gᶜ)` is the average degree of the complement of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture316 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    IsWellTotallyDominated G := by
  let P : Finset α := pendantVertices G
  let Q : Finset α := Finset.univ \ P
  have hQ : Q = Finset.univ \ P := rfl
  have hP : ∀ v ∈ P, G.degree v = 1 := by
    intro v hv
    simpa [P, pendantVertices] using hv
  change (averageDegree Gᶜ : ℚ) ≤ P.card at h
  by_cases hp : P.card = 0
  · have hcomp := average_compl_edge_bound G P h
    rw [hp, zero_mul] at hcomp
    have hcomp_zero : Gᶜ.edgeFinset.card = 0 := by omega
    have htotal := edge_count_add_compl G
    have hm : G.edgeFinset.card = (Fintype.card α).choose 2 := by omega
    exact wellTotallyDominated_of_eq_top G (eq_top_of_card_edgeFinset_eq_choose G hm)
  · have hp_pos : 0 < P.card := Nat.pos_of_ne_zero hp
    have hn_two : 2 ≤ Fintype.card α := Nat.succ_le_iff.mpr Fintype.one_lt_card
    by_cases hn : Fintype.card α = 2
    · have hlower := connected_edge_lower G hG
      have hupper := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
      have hm : G.edgeFinset.card = (Fintype.card α).choose 2 := by
        norm_num [hn] at hupper ⊢
        omega
      exact wellTotallyDominated_of_eq_top G (eq_top_of_card_edgeFinset_eq_choose G hm)
    · have hn_three : 3 ≤ Fintype.card α := by omega
      have hclique := nonpendant_isClique G hG P Q hQ hn_three hp_pos hP h
      have hleaf : ∀ v ∈ P, ∀ w, G.Adj v w → w ∈ Q := by
        intro v hvP w hvw
        rw [hQ]
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hwP
        have hcard := card_le_two_of_adjacent_degree_one G hG (hP v hvP) (hP w hwP) hvw
        omega
      exact wellTotallyDominated_of_pendant_core_clique G P Q hQ hp_pos hP hleaf hclique

-- Sanity checks

/-- The average degree of the edgeless graph on 3 vertices is 0. -/
@[category test, AMS 5]
example : averageDegree (⊥ : SimpleGraph (Fin 3)) = 0 := by
  unfold averageDegree; simp [Fintype.card_fin]

/-- In `P₃` (path 0-1-2), the average degree is 4/3 and there are 2 pendant vertices. -/
@[category test, AMS 5]
example : averageDegree (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 4/3 := by
  unfold averageDegree; decide +native

end WrittenOnTheWallII.GraphConjecture316
