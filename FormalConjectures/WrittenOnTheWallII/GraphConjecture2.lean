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


import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 2

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture2

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma exists_max_indep_set_in_nbhd (G : SimpleGraph α) (v : α) :
  ∃ A : Finset α, (A : Set α) ⊆ G.neighborSet v ∧
    IsAntichain G.Adj (A : Set α) ∧
    A.card = G.indepNeighborsCard v := by
  haveI := Classical.decEq α
  norm_num[SimpleGraph.indepNeighborsCard,IsAntichain,Set.subset_def]
  show∃_, _∧_∧_=(id _)
  norm_num[SimpleGraph.isNIndepSet_iff,Set.Pairwise]
  simp_rw [SupSet.sSup]
  split
  · simp_rw [comm.trans (Nat.find_eq_iff _)]
    push_neg
    choose _ _ _ using(Set.exists_max_image _) id (BddAbove.finite (by valid)) (by exact ⟨ _,{},nofun, rfl⟩)
    obtain ⟨A, B, rfl⟩:=‹∃l,_›
    classical use A.image (↑), Finset.forall_mem_image.2 fun and x =>and.2, Finset.forall_mem_image.2 fun and x => Finset.forall_mem_image.2 (B and and.2 x _ ·.2),by rwa[A.card_image_of_injective Subtype.coe_injective]
    use fun and k=>by exists _,⟨A,B,A.card_image_of_injective Subtype.coe_injective|>.symm⟩
  · bound

noncomputable def maxIndepSet (G : SimpleGraph α) (v : α) : Finset α :=
  Classical.choose (exists_max_indep_set_in_nbhd G v)

lemma sum_indepNeighbors_eq (G : SimpleGraph α) [DecidableRel G.Adj] :
  (∑ v, G.indepNeighbors v) = ∑ v, ((maxIndepSet G v).card : ℝ) := by
  delta GraphConjecture2.maxIndepSet indepNeighbors
  delta indepNeighborsCard Classical.choose
  refine Fintype.sum_congr _ _ fun and=>by cases↑(Classical.indefiniteDescription _ _) with aesop

lemma sum_card_eq_sum_din (G : SimpleGraph α) [DecidableRel G.Adj] :
  (∑ v, ((maxIndepSet G v).card : ℝ)) = ∑ x, ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) := by
  norm_num[←Nat.cast_sum,(Fintype.sum_congr _ _ fun and=>Finset.card_filter _ _).trans Finset.sum_comm]

lemma h_spanning_tree_lemma (G : SimpleGraph α) (h : G.Connected) :
  ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree := by
  have h_tree := h.exists_isTree_le
  rcases h_tree with ⟨T, h_le, h_isTree⟩
  let T_sub := SimpleGraph.toSubgraph T h_le
  use T_sub
  constructor
  · exact SimpleGraph.toSubgraph.isSpanning T h_le
  · simp_all [isTree_iff, T_sub]
    simp_all? (config := {singlePass :=1}) -contextual [SimpleGraph.isAcyclic_iff_forall_adj_isBridge, SimpleGraph.connected_iff_exists_forall_reachable]
    delta SimpleGraph.IsBridge at *
    use h_isTree.1.imp fun and a s=>(a s).elim (·.rec .rfl fun and x=>.trans (SimpleGraph.Adj.reachable and)), fun and R M=>⟨ M,(h_isTree.2 M).2 ∘.map ⟨Subtype.val,by norm_num[Subtype.eq_iff]⟩⟩

lemma max_leaf_tree_exists (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree ∧
  (G.Ls = (T.verts.toFinset.filter (fun v => T.degree v = 1)).card) := by
  let f := (fun T : G.Subgraph => (((T.verts.toFinset.filter (fun v => T.degree v = 1)).card) : ℝ))
  let S_set := {T : G.Subgraph | T.IsSpanning ∧ T.coe.IsTree}
  have h_S_fin : S_set.Finite := by apply Subtype.finite
  have h_S_ne : S_set.Nonempty := by
    rcases h_spanning_tree_lemma G h with ⟨T0, h_span, h_tree⟩
    use T0
    exact ⟨h_span, h_tree⟩
  have h_fS_fin : (f '' S_set).Finite := Set.Finite.image f h_S_fin
  have h_fS_ne : (f '' S_set).Nonempty := Set.Nonempty.image f h_S_ne
  have h_sSup_mem : sSup (f '' S_set) ∈ f '' S_set := by apply (by valid:).csSup_mem (by valid)
  have h_Ls_eq : G.Ls = sSup (f '' S_set) := by rfl
  rcases h_sSup_mem with ⟨T, h_T_mem, h_T_eq⟩
  use T
  rcases h_T_mem with ⟨h_span, h_tree⟩
  refine ⟨h_span, h_tree, ?_⟩
  rw [h_Ls_eq]
  exact h_T_eq.symm

lemma c_edge_bound_strong (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) (hxy : G.Adj x y) :
  ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) + ((Finset.univ.filter (fun v => y ∈ maxIndepSet G v)).card : ℝ) ≤ (G.neighborFinset x ∪ G.neighborFinset y).card := by
  have h_disjoint : Disjoint (Finset.univ.filter (fun v => x ∈ maxIndepSet G v)) (Finset.univ.filter (fun v => y ∈ maxIndepSet G v)) := by
    rw [Finset.disjoint_filter]
    intro v _ hx hy
    have h_anti : IsAntichain G.Adj (maxIndepSet G v : Set α) := (Classical.choose_spec (exists_max_indep_set_in_nbhd G v)).2.1
    have h_not_adj : ¬ G.Adj x y := h_anti hx hy (G.ne_of_adj hxy)
    exact h_not_adj hxy
  have h_card := Finset.card_union_of_disjoint h_disjoint
  have h_sub : (Finset.univ.filter (fun v => x ∈ maxIndepSet G v)) ∪ (Finset.univ.filter (fun v => y ∈ maxIndepSet G v)) ⊆ G.neighborFinset x ∪ G.neighborFinset y := by
    intro v hv
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hv
    rcases hv with ⟨_, hx⟩ | ⟨_, hy⟩
    · apply Finset.mem_union_left
      have h_sub_v := (Classical.choose_spec (exists_max_indep_set_in_nbhd G v)).1
      have h_adj := h_sub_v hx
      rw [SimpleGraph.mem_neighborFinset]
      exact G.symm h_adj
    · apply Finset.mem_union_right
      have h_sub_v := (Classical.choose_spec (exists_max_indep_set_in_nbhd G v)).1
      have h_adj := h_sub_v hy
      rw [SimpleGraph.mem_neighborFinset]
      exact G.symm h_adj
  have h_le := Finset.card_le_card h_sub
  rw [h_card] at h_le
  exact_mod_cast h_le

lemma tree_leaves_ge_degrees (G : SimpleGraph α) [DecidableRel G.Adj] (T : G.Subgraph) (hT : T.coe.IsTree) (x y : α) (hxy : T.Adj x y) :
  ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ) ≥ (T.degree x : ℝ) + (T.degree y : ℝ) - 2 := by
  let L := T.verts.toFinset.filter (fun v => T.degree v = 1)
  let Y := T.verts.toFinset.filter (fun v => T.degree v ≠ 1)
  have h_univ : T.verts.toFinset = L ∪ Y := by rw[ Finset.filter_union_filter_neg_eq]
  have h_disj : Disjoint L Y := by apply Finset.disjoint_filter_filter_neg
  have h_sum_deg : ∑ v ∈ T.verts.toFinset, (T.degree v : ℝ) = 2 * (T.verts.toFinset.card : ℝ) - 2 := by
    have' :=(hT).card_edgeFinset
    have:=T.coe.sum_degrees_eq_twice_card_edges
    linear_combination2(norm:=norm_num[SimpleGraph.degree, mul_add,SimpleGraph.neighborFinset_eq_filter,←‹_+1 = _›, Finset.sum_subtype _ fun and=>Set.mem_toFinset])congr_arg (. : ℕ → ℝ) this
    congr!
    delta SimpleGraph.Subgraph.degree
    simp_rw [ Fintype.card_subtype, Finset.card_filter]
    exact (symm (( Finset.sum_subset (T).verts.toFinset.subset_univ fun and I I =>if_neg (I ∘ (by ·norm_num [·.snd_mem]))).symm.trans ( Finset.sum_subtype ↑_ (by((((norm_num))))) _) ) )
  have h_sum_2 : ∑ v ∈ T.verts.toFinset, (2 : ℝ) = 2 * (T.verts.toFinset.card : ℝ) := by rw [←nsmul_eq_mul', Finset.sum_const]
  have h_diff : ∑ v ∈ T.verts.toFinset, ((T.degree v : ℝ) - 2) = -2 := by rw[ Finset.sum_sub_distrib,h_sum_deg,h_sum_2,sub_sub_cancel_left]
  have h_split : ∑ v ∈ T.verts.toFinset, ((T.degree v : ℝ) - 2) = (∑ v ∈ L, ((T.degree v : ℝ) - 2)) + (∑ v ∈ Y, ((T.degree v : ℝ) - 2)) := by rwa[h_univ, L.sum_union]
  have h_sum_L : ∑ v ∈ L, ((T.degree v : ℝ) - 2) = - (L.card : ℝ) := by exact (L.sum_congr rfl (by norm_num+contextual[L])).trans ( (L.sum_const (-1)).trans (by ring))
  have h_eq_Y : (L.card : ℝ) = 2 + ∑ v ∈ Y, ((T.degree v : ℝ) - 2) := by linear_combination h_split+h_sum_L-h_diff
  have h_Y_nonneg : ∀ v ∈ Y, 0 ≤ ((T.degree v : ℝ) - 2) := by
    use fun and μ=>sub_nonneg.mpr (mod_cast (Finset.mem_filter.mp μ).right.symm.lt_of_le (Finset.card_pos.mpr.comp (hT.1 ⟨ _,Set.mem_toFinset.1 ( Finset.filter_subset _ _ μ)⟩ ⟨x,?_⟩).elim ?_ ) )
    use hxy.fst_mem
    norm_num [ Finset.Nonempty]
    use (by cases. with. (bound ) )
  have h_x_Y_val : x ∈ Y → (T.degree x : ℝ) - 2 ≤ ∑ v ∈ Y, ((T.degree v : ℝ) - 2) := by apply Y.single_le_sum h_Y_nonneg
  have h_xy_Y_val : x ∈ Y → y ∈ Y → x ≠ y → ((T.degree x : ℝ) - 2) + ((T.degree y : ℝ) - 2) ≤ ∑ v ∈ Y, ((T.degree v : ℝ) - 2) := by convert Y.add_le_sum (by valid)
  use h_eq_Y▸ if a:_ then if I:_ then by linear_combination h_xy_Y_val a I hxy.ne else(? _)else(? _)
  · linear_combination(mod_cast (by_contra (I ∘by norm_num[Y,hxy.snd_mem])):(T.degree y: ℝ)=1)+h_x_Y_val a
  by_cases h2 :y ∈ Y
  · norm_num[Y,hxy.fst_mem]at a
    use a.symm▸by linear_combination Y.single_le_sum ‹_› h2
  · norm_num[not_not.1 (a ∘ Finset.mem_filter.2 ∘.intro _),not_not.1 (h2 ∘ Finset.mem_filter.2 ∘.intro _),hxy.fst_mem, T.edge_vert hxy.symm,Y,(le_add_of_nonneg_right<|Y.sum_nonneg h_Y_nonneg).trans']
    linear_combination(Y.card_nsmul_le_sum _ _ (sub_nonneg.1 ∘h_Y_nonneg ·)).trans' ((by rw []))

def DoubleStar (G : SimpleGraph α) (x y : α) (hxy : G.Adj x y) : SimpleGraph α where
  Adj u v :=
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) ∨
    (u = x ∧ G.Adj x v ∧ v ≠ y) ∨ (v = x ∧ G.Adj x u ∧ u ≠ y) ∨
    (u = y ∧ G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x) ∨ (v = y ∧ G.Adj y u ∧ ¬ G.Adj x u ∧ u ≠ x)
  symm := by
    intro u v huv
    rcases huv with h1 | h2 | h3 | h4 | h5 | h6
    · right; left; exact ⟨h1.2, h1.1⟩
    · left; exact ⟨h2.2, h2.1⟩
    · right; right; right; left; exact h3
    · right; right; left; exact h4
    · right; right; right; right; right; exact h5
    · right; right; right; right; left; exact h6
  loopless := by
    intro u huu
    rcases huu with h1 | h2 | h3 | h4 | h5 | h6
    · exact (G.ne_of_adj hxy) (h1.1.symm.trans h1.2)
    · exact (G.ne_of_adj hxy) (h2.2.symm.trans h2.1)
    · have h_adj : G.Adj x x := by
        have ht := h3.2.1
        rw [h3.1] at ht
        exact ht
      exact G.loopless x h_adj
    · have h_adj : G.Adj x x := by
        have ht := h4.2.1
        rw [h4.1] at ht
        exact ht
      exact G.loopless x h_adj
    · have h_adj : G.Adj y y := by
        have ht := h5.2.1
        rw [h5.1] at ht
        exact ht
      exact G.loopless y h_adj
    · have h_adj : G.Adj y y := by
        have ht := h6.2.1
        rw [h6.1] at ht
        exact ht
      exact G.loopless y h_adj

lemma DoubleStar_le (G : SimpleGraph α) (x y : α) (hxy : G.Adj x y) :
  DoubleStar G x y hxy ≤ G := by
  intro u v huv
  rcases huv with h1 | h2 | h3 | h4 | h5 | h6
  · rw [h1.1, h1.2]; exact hxy
  · rw [h2.1, h2.2]; exact G.symm hxy
  · rw [h3.1]; exact h3.2.1
  · rw [h4.1]; exact G.symm h4.2.1
  · rw [h5.1]; exact h5.2.1
  · rw [h6.1]; exact G.symm h6.2.1

lemma DoubleStar_isAcyclic (G : SimpleGraph α) (x y : α) (hxy : G.Adj x y) :
  (DoubleStar G x y hxy).IsAcyclic := by
  delta DoubleStar SimpleGraph.IsAcyclic
  rintro c(A|⟨_, _, _⟩) and
  · simp_all
  · use SimpleGraph.Adj.ne (by valid) rfl
  cases‹SimpleGraph.Walk _ _ _› with|nil=>rcases and.three_le_length.not_gt (by constructor) | cons=>_
  simp_all-contextual[SimpleGraph.Walk.isCycle_def, G.adj_comm,←or_and_right,←and_or_left,←or_assoc]
  obtain ⟨@c, rfl⟩|⟨@c, rfl⟩|⟨@c, H, _⟩|⟨@c, I, _⟩|⟨@c, L, _⟩|⟨@c, M, _⟩:=‹_ ∨_›
  · simp_all
  · simp_all[Int, G.adj_comm]
  · simp_all[G.adj_comm]
    cases‹SimpleGraph.Walk _ _ _› with aesop
  · simp_all[I.ne']
  · simp_all[eq_comm, G.adj_comm]
    cases‹SimpleGraph.Walk _ _ _› with aesop
  · simp_all[and.2,M.ne']

lemma exists_maximal_acyclic (G : SimpleGraph α) (H : SimpleGraph α) (hH_le : H ≤ G) (hH_acyc : H.IsAcyclic) :
  ∃ T : SimpleGraph α, T ≤ G ∧ T.IsAcyclic ∧ H ≤ T ∧ ∀ T' : SimpleGraph α, T' ≤ G → T'.IsAcyclic → T ≤ T' → T' = T := by cases Set.exists_max_image {S≤G | S.IsAcyclic ∧H≤S} (Set.ncard {S≤G | S≤·}) Subtype.finite (by exists@H)
                                                                                                                         exact (by assumption :).elim fun ⟨A, B, C⟩ h=>⟨ _,A, B, C, fun and a s R=>le_antisymm (Set.eq_of_subset_of_ncard_le (by gcongr) (h and ⟨a,s,.trans C R⟩) |>.ge (by use a)).2 R⟩

def AddEdge (T : SimpleGraph α) (a b : α) (h_neq : a ≠ b) : SimpleGraph α where
  Adj u v := T.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  symm := by
    intro u v huv
    rcases huv with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (T.symm h)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless := by
    intro u huu
    rcases huu with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact T.loopless u h
    · exact h_neq rfl
    · exact h_neq.symm rfl

lemma AddEdge_le (T G : SimpleGraph α) (a b : α) (h_neq : a ≠ b) (hT_le : T ≤ G) (hab : G.Adj a b) :
  AddEdge T a b h_neq ≤ G := by
  intro u v huv
  rcases huv with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hT_le h
  · exact hab
  · exact G.symm hab

lemma T_le_AddEdge (T : SimpleGraph α) (a b : α) (h_neq : a ≠ b) :
  T ≤ AddEdge T a b h_neq := by
  intro u v huv
  exact Or.inl huv

lemma Reachable_AddEdge_walk (T : SimpleGraph α) (a b : α) (h_neq : a ≠ b) {x y : α} (p : (AddEdge T a b h_neq).Walk x y) :
  T.Reachable x y ∨ (T.Reachable x a ∧ T.Reachable b y) ∨ (T.Reachable x b ∧ T.Reachable a y) := by
  induction p with
  | nil =>
    left
    exact SimpleGraph.Reachable.refl _
  | cons h_adj _ ih =>
    rcases ih with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
    · rcases h_adj with hT | ⟨hx, hv⟩ | ⟨hx, hv⟩
      · left
        exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hT) h1
      · right
        left
        cases hx; cases hv
        exact ⟨SimpleGraph.Reachable.refl a, h1⟩
      · right
        right
        cases hx; cases hv
        exact ⟨SimpleGraph.Reachable.refl b, h1⟩
    · rcases h_adj with hT | ⟨hx, hv⟩ | ⟨hx, hv⟩
      · right
        left
        exact ⟨SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hT) h2a, h2b⟩
      · right
        left
        cases hx; cases hv
        exact ⟨SimpleGraph.Reachable.refl a, h2b⟩
      · left
        cases hx; cases hv
        exact h2b
    · rcases h_adj with hT | ⟨hx, hv⟩ | ⟨hx, hv⟩
      · right
        right
        exact ⟨SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hT) h3a, h3b⟩
      · left
        cases hx; cases hv
        exact h3b
      · right
        right
        cases hx; cases hv
        exact ⟨SimpleGraph.Reachable.refl b, h3b⟩

lemma Reachable_AddEdge (T : SimpleGraph α) (a b : α) (h_neq : a ≠ b) (x y : α) (h_reach : (AddEdge T a b h_neq).Reachable x y) :
  T.Reachable x y ∨ (T.Reachable x a ∧ T.Reachable b y) ∨ (T.Reachable x b ∧ T.Reachable a y) := by
  rcases h_reach with ⟨p⟩
  exact Reachable_AddEdge_walk T a b h_neq p

lemma AddEdge_isAcyclic (T : SimpleGraph α) (a b : α) (h_neq : a ≠ b) (hT_acyc : T.IsAcyclic) (h_unreach : ¬ T.Reachable a b) :
  (AddEdge T a b h_neq).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    rw [SimpleGraph.isBridge_iff]
    constructor
    · exact he
    · intro h_reach
      have h_or : s(u,v) = s(a,b) ∨ s(u,v) ≠ s(a,b) := eq_or_ne s(u,v) s(a,b)
      rcases h_or with h_eq | h_neq_e
      · have h_T_eq : (AddEdge T a b h_neq) \ SimpleGraph.fromEdgeSet {s(u,v)} = T := by
          ext x y
          constructor
          · intro h
            have h_adj := h.1
            have h_not_e := h.2
            rw [h_eq] at h_not_e
            rcases h_adj with hT | ⟨hx, hy⟩ | ⟨hx, hy⟩
            · exact hT
            · exfalso; apply h_not_e; rw [hx, hy, SimpleGraph.fromEdgeSet_adj]; exact ⟨Set.mem_singleton s(a,b), h_neq⟩
            · exfalso; apply h_not_e; rw [hx, hy, SimpleGraph.fromEdgeSet_adj]; exact ⟨Sym2.eq_swap, h_neq.symm⟩
          · intro hT
            constructor
            · left; exact hT
            · intro h_eq_e
              have h_eq_sym2 : s(x, y) = s(a, b) := by
                rw [SimpleGraph.fromEdgeSet_adj] at h_eq_e
                rw [h_eq] at h_eq_e
                exact h_eq_e.1
              have h_reach_ab : T.Reachable a b := by
                have h_adj_ab : T.Adj a b := by
                  have h_cases := Sym2.eq_iff.mp h_eq_sym2
                  rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hT
                  · exact T.symm hT
                exact SimpleGraph.Adj.reachable h_adj_ab
              exact h_unreach h_reach_ab
        rw [h_T_eq] at h_reach
        have h_reach_ab : T.Reachable a b := by
          have h_sym2 : s(u, v) = s(a, b) := h_eq
          have h_cases := Sym2.eq_iff.mp h_sym2
          rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h_reach
          · exact h_reach.symm
        exact h_unreach h_reach_ab
      · have hT'_eq : AddEdge (T \ SimpleGraph.fromEdgeSet {s(u,v)}) a b h_neq = AddEdge T a b h_neq \ SimpleGraph.fromEdgeSet {s(u,v)} := by
          ext x y
          constructor
          · rintro (⟨hT, h_not_e⟩ | h_ab | h_ba)
            · exact ⟨Or.inl hT, h_not_e⟩
            · refine ⟨Or.inr (Or.inl h_ab), ?_⟩
              intro h_eq_e
              have h_eq_sym : s(x, y) = s(u, v) := Set.mem_singleton_iff.mp h_eq_e.1
              have h_x : x = a := h_ab.1
              have h_y : y = b := h_ab.2
              rw [h_x, h_y] at h_eq_sym
              exact h_neq_e h_eq_sym.symm
            · refine ⟨Or.inr (Or.inr h_ba), ?_⟩
              intro h_eq_e
              have h_eq_sym : s(x, y) = s(u, v) := Set.mem_singleton_iff.mp h_eq_e.1
              have h_x : x = b := h_ba.1
              have h_y : y = a := h_ba.2
              rw [h_x, h_y] at h_eq_sym
              have h_sym_ab : s(b, a) = s(a, b) := Sym2.eq_swap
              rw [h_sym_ab] at h_eq_sym
              exact h_neq_e h_eq_sym.symm
          · rintro ⟨h_adj, h_not_e⟩
            rcases h_adj with hT | h_ab | h_ba
            · exact Or.inl ⟨hT, h_not_e⟩
            · exact Or.inr (Or.inl h_ab)
            · exact Or.inr (Or.inr h_ba)
        rw [← hT'_eq] at h_reach
        have h_reach_T' := Reachable_AddEdge (T \ SimpleGraph.fromEdgeSet {s(u,v)}) a b h_neq u v h_reach
        have h_T_bridge : T.IsBridge s(u,v) := by
          have hT_acyc_copy := hT_acyc
          rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge] at hT_acyc_copy
          have he_T : s(u,v) ∈ T.edgeSet := by
            have h_he := he
            rcases h_he with hT_edge | h_ab | h_ba
            · exact hT_edge
            · have hx : u = a := h_ab.1; have hy : v = b := h_ab.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e rfl
            · have hx : u = b := h_ba.1; have hy : v = a := h_ba.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e Sym2.eq_swap
          exact hT_acyc_copy he_T
        have h_not_reach : ¬ (T \ SimpleGraph.fromEdgeSet {s(u,v)}).Reachable u v := by
          rw [SimpleGraph.isBridge_iff] at h_T_bridge
          exact h_T_bridge.2
        rcases h_reach_T' with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
        · exact h_not_reach h1
        · have h_reach_ab : T.Reachable a b := by
            have h_ua : T.Reachable u a := by
              have h_sub : (T \ SimpleGraph.fromEdgeSet {s(u,v)}) ≤ T := sdiff_le
              exact SimpleGraph.Reachable.mono h_sub h2a
            have h_bv : T.Reachable b v := by
              have h_sub : (T \ SimpleGraph.fromEdgeSet {s(u,v)}) ≤ T := sdiff_le
              exact SimpleGraph.Reachable.mono h_sub h2b
            have h_au : T.Reachable a u := SimpleGraph.Reachable.symm h_ua
            have h_uv : T.Reachable u v := by
              have h_adj_uv : T.Adj u v := by
                have h_he := he
                rcases h_he with hT_edge | h_ab | h_ba
                · exact hT_edge
                · have hx : u = a := h_ab.1; have hy : v = b := h_ab.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e rfl
                · have hx : u = b := h_ba.1; have hy : v = a := h_ba.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e Sym2.eq_swap
              exact SimpleGraph.Adj.reachable h_adj_uv
            have h_av : T.Reachable a v := SimpleGraph.Reachable.trans h_au h_uv
            have h_vb : T.Reachable v b := SimpleGraph.Reachable.symm h_bv
            exact SimpleGraph.Reachable.trans h_av h_vb
          exact h_unreach h_reach_ab
        · have h_reach_ab : T.Reachable a b := by
            have h_ub : T.Reachable u b := by
              have h_sub : (T \ SimpleGraph.fromEdgeSet {s(u,v)}) ≤ T := sdiff_le
              exact SimpleGraph.Reachable.mono h_sub h3a
            have h_av : T.Reachable a v := by
              have h_sub : (T \ SimpleGraph.fromEdgeSet {s(u,v)}) ≤ T := sdiff_le
              exact SimpleGraph.Reachable.mono h_sub h3b
            have h_bu : T.Reachable b u := SimpleGraph.Reachable.symm h_ub
            have h_uv : T.Reachable u v := by
              have h_adj_uv : T.Adj u v := by
                have h_he := he
                rcases h_he with hT_edge | h_ab | h_ba
                · exact hT_edge
                · have hx : u = a := h_ab.1; have hy : v = b := h_ab.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e rfl
                · have hx : u = b := h_ba.1; have hy : v = a := h_ba.2; rw [hx, hy] at h_neq_e; exfalso; exact h_neq_e Sym2.eq_swap
              exact SimpleGraph.Adj.reachable h_adj_uv
            have h_bv : T.Reachable b v := SimpleGraph.Reachable.trans h_bu h_uv
            have h_va : T.Reachable v a := SimpleGraph.Reachable.symm h_av
            have h_ba_reach : T.Reachable b a := SimpleGraph.Reachable.trans h_bv h_va
            exact SimpleGraph.Reachable.symm h_ba_reach
          exact h_unreach h_reach_ab

lemma walk_leaves_C (G T : SimpleGraph α) (u v w : α) (h_reach : G.Reachable v w)
  (hv : T.Reachable u v) (hw : ¬ T.Reachable u w) :
  ∃ a b, G.Adj a b ∧ T.Reachable u a ∧ ¬ T.Reachable u b := by convert (by_contra) (hw ∘h_reach.elim ∘ fun and x =>x.rec ↑id (@ _) @hv)
                                                               grind

lemma reachable_edge (G : SimpleGraph α) (h : G.Connected) (T : SimpleGraph α) (h_not_conn : ¬ T.Connected) :
  ∃ a b : α, G.Adj a b ∧ ¬ T.Reachable a b := by
  have h_ex : ∃ u v, ¬ T.Reachable u v := by
    by_contra h_all
    push_neg at h_all
    have hT_conn : T.Connected := ⟨h_all⟩
    exact h_not_conn hT_conn
  rcases h_ex with ⟨u, v, huv⟩
  have h_walk : G.Reachable u v := h.preconnected u v
  have ha_reach : T.Reachable u u := SimpleGraph.Reachable.refl u
  have ⟨a, b, hab, ha, hb⟩ := walk_leaves_C G T u u v h_walk ha_reach huv
  use a, b
  refine ⟨hab, ?_⟩
  intro h_reach_ab
  have h_reach_ub : T.Reachable u b := SimpleGraph.Reachable.trans ha h_reach_ab
  exact hb h_reach_ub

lemma maximal_acyclic_is_connected (G : SimpleGraph α) (h : G.Connected)
  (T : SimpleGraph α) (hT_le : T ≤ G) (hT_acyc : T.IsAcyclic)
  (hT_max : ∀ T' : SimpleGraph α, T' ≤ G → T'.IsAcyclic → T ≤ T' → T' = T) :
  T.Connected := by
  by_contra h_not_conn
  have ⟨a, b, hab, h_unreach⟩ := reachable_edge G h T h_not_conn
  have h_neq : a ≠ b := by use hab.ne
  let T' := AddEdge T a b h_neq
  have hT'_le : T' ≤ G := AddEdge_le T G a b h_neq hT_le hab
  have hT'_acyc : T'.IsAcyclic := AddEdge_isAcyclic T a b h_neq hT_acyc h_unreach
  have hT_le_T' : T ≤ T' := T_le_AddEdge T a b h_neq
  have h_eq := hT_max T' hT'_le hT'_acyc hT_le_T'
  have h_adj : T'.Adj a b := Or.inr (Or.inl ⟨rfl, rfl⟩)
  rw [h_eq] at h_adj
  have h_reach : T.Reachable a b := by exact (h_adj).reachable
  exact h_unreach h_reach

lemma exists_optimal_tree (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (x y : α) (hxy : G.Adj x y) :
  ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree ∧ T.Adj x y ∧
  (∀ v ∈ G.neighborFinset x, T.Adj x v) ∧ (∀ v ∈ G.neighborFinset y \ G.neighborFinset x, T.Adj y v) := by
  let H := DoubleStar G x y hxy
  have hH_le := DoubleStar_le G x y hxy
  have hH_acyc := DoubleStar_isAcyclic G x y hxy
  have ⟨T_graph, hT_le, hT_acyc, hH_T, hT_max⟩ := exists_maximal_acyclic G H hH_le hH_acyc
  have hT_conn := maximal_acyclic_is_connected G h T_graph hT_le hT_acyc hT_max
  let T_sub := SimpleGraph.toSubgraph T_graph hT_le
  use T_sub
  have hT_isTree : T_sub.coe.IsTree := by norm_num[SimpleGraph.isTree_iff,T_sub]
                                          norm_num[SimpleGraph.IsAcyclic, T_sub,SimpleGraph.connected_iff_exists_forall_reachable] at hT_conn hT_acyc⊢
                                          use hT_conn.imp fun and R M=>(R M).elim (·.rec .rfl fun and x=>.trans (SimpleGraph.Adj.reachable and)), fun and R M=>hT_acyc (R.map ⟨Subtype.val,by bound⟩) (by norm_num[M.map])
  have h_prop1 : T_sub.Adj x y := by norm_num[H, T_sub] at hH_T⊢
                                     use hH_T (by tauto)
  have h_prop2 : ∀ v ∈ G.neighborFinset x, T_sub.Adj x v := by norm_num[H, T_sub] at h_prop1 hH_T⊢
                                                               use fun and k=>hH_T (.symm (by tauto))
  have h_prop3 : ∀ v ∈ G.neighborFinset y \ G.neighborFinset x, T_sub.Adj y v := by norm_num[SimpleGraph.isAcyclic_iff_forall_adj_isBridge, T_sub] at h_prop1 h_prop2 hT_max⊢
                                                                                    use fun and R M=>hH_T (.symm (by tauto))
  exact ⟨SimpleGraph.toSubgraph.isSpanning T_graph hT_le, hT_isTree, h_prop1, h_prop2, h_prop3⟩

lemma union_neighbor_bound (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (x y : α) (hxy : G.Adj x y) :
  ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤ G.Ls + 2 := by
  have h_opt := exists_optimal_tree G h x y hxy
  rcases h_opt with ⟨T, h_span, h_tree, hT_xy, hT_x, hT_y⟩
  have h_leaves_ge := tree_leaves_ge_degrees G T h_tree x y hT_xy
  have h_Ls_ge : ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ) ≤ G.Ls := by delta SimpleGraph.Ls and SimpleGraph.Subgraph.IsSpanning SimpleGraph.Subgraph.degree at*
                                                                                             exact (le_csSup ⟨ Fintype.card α,Set.forall_mem_image.2 fun and m=>mod_cast(Finset.card_le_univ _).trans ( (by bound))⟩ (by exists T))
  have h_deg_x : (T.degree x : ℝ) ≥ ((G.neighborFinset x).card : ℝ) := by push_cast[SimpleGraph.Subgraph.degree, false,SimpleGraph.neighborFinset_eq_filter]
                                                                          exact (mod_cast(Fintype.card_subtype _).ge.trans' (Finset.card_mono fun and=>by simp_all) )
  have h_deg_y : (T.degree y : ℝ) ≥ ((G.neighborFinset y \ G.neighborFinset x).card : ℝ) := by delta SimpleGraph.Subgraph.degree
                                                                                               exact (mod_cast(Fintype.card_coe _)▸ Fintype.card_le_of_injective (⟨ _,(hT_y _) ·.2⟩) fun and x=>and.eq ∘by norm_num[a.-h])
  have h_union : ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) = ((G.neighborFinset x).card : ℝ) + ((G.neighborFinset y \ G.neighborFinset x).card : ℝ) := by rw [←Nat.cast_add,← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  linarith

lemma c_edge_Ls_bound (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (x y : α) (hxy : G.Adj x y) :
  ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) + ((Finset.univ.filter (fun v => y ∈ maxIndepSet G v)).card : ℝ) ≤ G.Ls + 2 := by
  have h1 := c_edge_bound_strong G x y hxy
  have h2 := union_neighbor_bound G h x y hxy
  linarith

lemma c_edge_bound (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) (hxy : G.Adj x y) :
  ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) + ((Finset.univ.filter (fun v => y ∈ maxIndepSet G v)).card : ℝ) ≤ Fintype.card α := by
  have h_disjoint : Disjoint (Finset.univ.filter (fun v => x ∈ maxIndepSet G v)) (Finset.univ.filter (fun v => y ∈ maxIndepSet G v)) := by
    rw [Finset.disjoint_filter]
    intro v _ hx hy
    have h_anti : IsAntichain G.Adj (maxIndepSet G v : Set α) := (Classical.choose_spec (exists_max_indep_set_in_nbhd G v)).2.1
    have h_not_adj : ¬ G.Adj x y := h_anti hx hy (G.ne_of_adj hxy)
    exact h_not_adj hxy
  have h_card := Finset.card_union_of_disjoint h_disjoint
  have h_sub := Finset.card_le_card (Finset.subset_univ (Finset.univ.filter (fun v => x ∈ maxIndepSet G v) ∪ Finset.univ.filter (fun v => y ∈ maxIndepSet G v)))
  rw [h_card] at h_sub
  exact_mod_cast h_sub

lemma c_deg_bound (G : SimpleGraph α) [DecidableRel G.Adj] (x : α) :
  ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) ≤ G.degree x := by
  have h_sub : (Finset.univ.filter (fun v => x ∈ maxIndepSet G v)) ⊆ G.neighborFinset x := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h_sub2 := (Classical.choose_spec (exists_max_indep_set_in_nbhd G v)).1
    have h_adj : G.Adj v x := h_sub2 hv.2
    rw [SimpleGraph.mem_neighborFinset]
    exact G.symm h_adj
  exact_mod_cast Finset.card_le_card h_sub

noncomputable def S_heavy (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun x => (G.Ls : ℝ) / 2 + 1 < ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ))

lemma S_heavy_is_indep (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  G.IsIndepSet (S_heavy G : Set α) := by
  intro x hx y hy h_neq h_adj
  rw [Finset.mem_coe] at hx hy
  have hx' : x ∈ S_heavy G := hx
  have hy' : y ∈ S_heavy G := hy
  rw [S_heavy, Finset.mem_filter] at hx' hy'
  have h1 := hx'.2
  have h2 := hy'.2
  have h3 := c_edge_Ls_bound G h x y h_adj
  linarith

lemma S_heavy_inter_bound (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (y : α) :
  ((G.neighborFinset y ∩ S_heavy G).card : ℝ) ≤ (G.Ls : ℝ) / 2 + 1 := by
  let I := G.neighborFinset y ∩ S_heavy G
  by_cases h_emp : I = ∅
  · have h1 : I.card = 0 := Finset.card_eq_zero.mpr h_emp
    have h2 : (I.card : ℝ) = 0 := by exact_mod_cast h1
    have h3 : 0 ≤ G.Ls / 2 + 1 := by norm_num[SimpleGraph.Ls,div_nonneg, add_nonneg]
                                     exact add_nonneg (div_nonneg ( Real.sSup_nonneg fun and true => true.elim (by bound)) (2).cast_nonneg) (zero_le_one)
    linarith
  · have h_ne : I.Nonempty := Finset.nonempty_of_ne_empty h_emp
    rcases h_ne with ⟨x, hx⟩
    have hx_S : x ∈ S_heavy G := Finset.mem_inter.mp hx |>.2
    have hx_N : x ∈ G.neighborFinset y := Finset.mem_inter.mp hx |>.1
    have hxy : G.Adj x y := by exact (.symm (by simp_all ) )
    have h_union := union_neighbor_bound G h x y hxy
    have h_indep := S_heavy_is_indep G h
    have h_disj : Disjoint I (G.neighborFinset x) := by refine Finset.disjoint_left.mpr fun and R M=>by norm_num [h_indep hx_S (Finset.inter_subset_right R) ∘mt (·▸ M)] at M
    have h_sub : I ∪ G.neighborFinset x ⊆ G.neighborFinset y ∪ G.neighborFinset x := by norm_num[I, I.union_subset_union]
    have h_card := Finset.card_union_of_disjoint h_disj
    have h_le := Finset.card_le_card h_sub
    have h_c_x : (G.Ls : ℝ) / 2 + 1 < ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) := by
      have h1 : x ∈ S_heavy G ↔ x ∈ Finset.univ ∧ (G.Ls : ℝ) / 2 + 1 < ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) := Finset.mem_filter
      exact (h1.mp hx_S).2
    have h_deg_x : ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) ≤ G.degree x := c_deg_bound G x
    have h_deg_x_val : ((G.neighborFinset x).card : ℝ) = G.degree x := by rfl
    have h_le_R : (I.card : ℝ) + ((G.neighborFinset x).card : ℝ) ≤ ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) := by use mod_cast by rwa[Finset.union_comm,<-h_card]
    linarith

lemma fms_algebraic_sum (G : SimpleGraph α) [DecidableRel G.Adj] (c : α → ℝ) (μ : ℝ)
  (hμ_pos : 0 ≤ μ)
  (hc_deg : ∀ x, c x ≤ G.degree x)
  (hc_edge : ∀ x y, G.Adj x y → c x + c y ≤ 2 * μ)
  (S : Finset α)
  (hS_indep : G.IsIndepSet (S : Set α))
  (hS_def : ∀ x, x ∈ S ↔ μ < c x)
  (h_I_bound : ∀ y, y ∉ S → ((G.neighborFinset y ∩ S).card : ℝ) ≤ μ) :
  ∑ x, c x ≤ (Fintype.card α : ℝ) * μ := by
  let Y := Finset.univ \ S
  have h_univ : Finset.univ = S ∪ Y := by norm_num [ Y]
  have h_disj : Disjoint S Y := by convert S.disjoint_sdiff
  have hY_def : ∀ y ∈ Y, c y ≤ μ := by norm_num [Y, true,hS_def]

  let W := fun x y => if x ∈ S ∧ G.Adj x y then (μ - c y) / (G.degree x : ℝ) else 0

  have h_W_x : ∀ x ∈ S, c x - μ ≤ ∑ y, W x y := by
    norm_num[← G.neighborFinset_eq_filter, W, two_mul, Finset.sum_ite] at hc_edge⊢
    use fun and i=>sub_le_iff_le_add.1 (( Finset.sum_le_sum fun a s=>div_le_div_of_nonneg_right (by linear_combination hc_edge and a (Finset.mem_filter.1 s).2.2:c and-μ≤ _) (by bound)).trans' ? _)
    norm_num[i, mul_div_cancel₀ _,← G.neighborFinset_eq_filter,(hμ_pos.trans_lt (((hS_def _).1 i).trans_le (hc_deg and))).ne']

  have h_W_y_S : ∀ y ∈ S, ∑ x, W x y = 0 := by exact fun and β=> Finset.sum_eq_zero fun and γ=>if_neg (And.elim (hS_indep · β ·.ne (by assumption)))

  have h_W_y_Y : ∀ y ∈ Y, ∑ x, W x y ≤ μ - c y := by
    norm_num[SimpleGraph.degree, G.neighborFinset_eq_filter, W, G.adj_comm,Y,ite_and, Finset.sum_ite, Finset.inter_comm] at h_I_bound⊢
    use fun and x =>( Finset.sum_le_card_nsmul _ _ _ fun a s=>div_le_div_of_nonneg_left (sub_nonneg.2 (hY_def _ (by norm_num[x,Y]))) ?_ (Nat.cast_le.2 (?_: ( S.filter (G.Adj and)).card≤_))).trans (?_)
    · bound[ Finset.card_pos.2 (by use a)]
    · use Nat.cast_le.1 (.trans (by rw [ Finset.inter_filter, S.inter_univ]) ((h_I_bound and x).trans (((hS_def _).1 (( S.filter_subset _) s)).le.trans ( (hc_deg a).trans (by norm_num[SimpleGraph.degree, G.neighborFinset_eq_filter])))))
    cases(S.filter (G.Adj and)).eq_empty_or_nonempty with| inl R=>norm_num[x,hY_def, R,Y]| inr=>_
    norm_num[ (by valid:).card_ne_zero, mul_div_cancel₀]

  have h_sum_W_S : ∑ x ∈ S, (c x - μ) ≤ ∑ x ∈ S, ∑ y, W x y := by refine S.sum_le_sum h_W_x

  have h_sum_swap : ∑ x ∈ S, ∑ y, W x y = ∑ y, ∑ x ∈ S, W x y := by apply S.sum_comm

  have h_sum_W_Y : ∑ y, ∑ x ∈ S, W x y = ∑ y ∈ Y, ∑ x ∈ S, W x y := by exact (Y.sum_subset Y.subset_univ fun and A B=>S.sum_eq_zero fun and(a)=>if_neg (B.comp ( Finset.mem_sdiff.2 ⟨A,fun R=>by linarith only[hc_edge _ _ ·.2,(hS_def _).1 R,(hS_def _).1 a]⟩))).symm

  have h_W_Y_le : ∑ y ∈ Y, ∑ x ∈ S, W x y ≤ ∑ y ∈ Y, (μ - c y) := by use Y.sum_le_sum fun and(A) =>(S.sum_subset S.subset_univ fun and a s=>if_neg (s ·.1)).trans_le (by apply_rules)

  have h_main : ∑ x ∈ S, (c x - μ) ≤ ∑ y ∈ Y, (μ - c y) := by linarith

  have h_final : ∑ x, c x ≤ (Fintype.card α : ℝ) * μ := by
    use(h_univ▸ S.sum_union (by valid)).trans_le ((ge_of_eq (by rw [ Fintype.card])).trans' ? _)
    exact (ge_of_eq (by rw [h_univ, S.card_union_of_disjoint (by assumption), Nat.cast_add, add_mul])).trans' (by linear_combination (h_main.trans (by rw [Y.sum_sub_distrib, Y.sum_const])).trans' (by rw [S.sum_sub_distrib, S.sum_const]))
  exact h_final






lemma fms_combinatorial_core (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  (∑ x, ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ)) ≤ (Fintype.card α : ℝ) * (G.Ls / 2 + 1) := by
  let c := fun x => ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ)
  let μ := G.Ls / 2 + 1
  let S := S_heavy G
  have hc_deg : ∀ x, c x ≤ G.degree x := c_deg_bound G
  have hc_edge : ∀ x y, G.Adj x y → c x + c y ≤ 2 * μ := by
    intro x y hxy
    have h1 := c_edge_Ls_bound G h x y hxy
    have h_eq : 2 * μ = G.Ls + 2 := by
      calc
        2 * (G.Ls / 2 + 1) = 2 * (G.Ls / 2) + 2 * 1 := mul_add 2 _ 1
        _ = G.Ls + 2 := by ring
    linarith
  have hS_indep : G.IsIndepSet (S : Set α) := S_heavy_is_indep G h
  have hS_def : ∀ x, x ∈ S ↔ μ < c x := by
    intro x
    have h1 : x ∈ S_heavy G ↔ x ∈ Finset.univ ∧ μ < c x := Finset.mem_filter
    simp only [Finset.mem_univ, true_and] at h1
    exact h1
  have h_I_bound : ∀ y, y ∉ S → ((G.neighborFinset y ∩ S).card : ℝ) ≤ μ := by
    intro y _
    exact S_heavy_inter_bound G h y
  have hμ_pos : 0 ≤ μ := by
    have h_ex := max_leaf_tree_exists G h
    rcases h_ex with ⟨T, _, _, h_eq⟩
    have h_card_nonneg : 0 ≤ (((T.verts.toFinset.filter (fun v => T.degree v = 1)).card) : ℝ) := Nat.cast_nonneg _
    dsimp [μ]
    rw [h_eq]
    linarith
  exact fms_algebraic_sum G c μ hμ_pos hc_deg hc_edge S hS_indep hS_def h_I_bound

lemma fms_lemma (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  ∑ v, G.indepNeighbors v ≤ (Fintype.card α : ℝ) * (G.Ls / 2 + 1) := by
  have h1 : (∑ v, G.indepNeighbors v) = ∑ v, ((maxIndepSet G v).card : ℝ) := sum_indepNeighbors_eq G
  have h2 : (∑ v, ((maxIndepSet G v).card : ℝ)) = ∑ x, ((Finset.univ.filter (fun v => x ∈ maxIndepSet G v)).card : ℝ) := sum_card_eq_sum_din G
  rw [h1, h2]
  exact fms_combinatorial_core G h

lemma l_le_Ls_div_2_plus_1 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  G.l ≤ G.Ls / 2 + 1 := by
  have h1 : G.l = (∑ v, G.indepNeighbors v) / (Fintype.card α : ℝ) := rfl
  have h2 : ∑ v, G.indepNeighbors v ≤ (Fintype.card α : ℝ) * (G.Ls / 2 + 1) := fms_lemma G h
  have h3 : (0 : ℝ) < Fintype.card α := by
    have h_ne : Fintype.card α ≠ 0 := Fintype.card_ne_zero
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_ne)
  have h4 : G.l * (Fintype.card α : ℝ) = ∑ v, G.indepNeighbors v := by
    rw [h1]
    exact div_mul_cancel₀ _ (ne_of_gt h3)
  rw [← h4] at h2
  have h5 : G.l * (Fintype.card α : ℝ) ≤ (G.Ls / 2 + 1) * (Fintype.card α : ℝ) := by
    calc
      G.l * (Fintype.card α : ℝ) ≤ (Fintype.card α : ℝ) * (G.Ls / 2 + 1) := h2
      _ = (G.Ls / 2 + 1) * (Fintype.card α : ℝ) := mul_comm _ _
  exact (mul_le_mul_iff_of_pos_right h3).mp h5



/--
WOWII [Conjecture 2](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`Ls(G) ≥ 2 · (l(G) - 1)` where `l(G)` is the average independence number of
the neighbourhoods of the vertices of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture2 (G : SimpleGraph α) (h : G.Connected) :
  2 * (l G - 1) ≤ Ls G := by
  have h1 : G.l = l G := rfl
  have h2 : G.Ls = Ls G := rfl
  have h3 : G.l ≤ G.Ls / 2 + 1 := l_le_Ls_div_2_plus_1 G h
  linarith

end WrittenOnTheWallII.GraphConjecture2
