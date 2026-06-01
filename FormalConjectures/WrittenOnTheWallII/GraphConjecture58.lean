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
# Written on the Wall II - Conjecture 58

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. A counterexample is given by taking $K_{3,3}$
(with bipartition $\{0,1,2\}$, $\{3,4,5\}$) and $K_{73}$ (on vertices $\{6,\ldots,78\}$),
then adding edges between vertex $0$ and every vertex of $K_{73}$.

This graph $G$ has $n = 79$ vertices and satisfies:
- $b(G) \ge 7$: the set $\{0,1,2,3,4,5,6\}$ induces a bipartite subgraph
- $f(G) \le 6$: the largest induced forest has at most 6 vertices
- $l_{\mathrm{avg}}(G) = 92/79$
- $\lceil b(G) / l_{\mathrm{avg}}(G) \rceil \ge 7 > 6 \ge f(G)$
-/

namespace WrittenOnTheWallII.GraphConjecture58

open SimpleGraph Finset

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

/-- The counterexample graph on `Fin 79`:
- K_{3,3}: bipartition {0,1,2} vs {3,4,5}
- K_73: complete graph on {6,...,78}
- Bridge: vertex 0 adjacent to all of {6,...,78} -/
private def counterG : SimpleGraph (Fin 79) where
  Adj u v :=
    u ≠ v ∧ (
      -- K_{3,3} edges: one vertex in {0,1,2}, other in {3,4,5}
      ((u.val < 3 ∧ 3 ≤ v.val ∧ v.val < 6) ∨ (v.val < 3 ∧ 3 ≤ u.val ∧ u.val < 6))
      -- K_73 edges: both vertices in {6,...,78}
      ∨ (6 ≤ u.val ∧ 6 ≤ v.val)
      -- Bridge edges: vertex 0 with any vertex in {6,...,78}
      ∨ (u.val = 0 ∧ 6 ≤ v.val)
      ∨ (v.val = 0 ∧ 6 ≤ u.val)
    )
  symm u v h := by
    obtain ⟨hne, hcases⟩ := h
    exact ⟨hne.symm, by tauto⟩
  loopless u h := h.1 rfl

private instance counterG_decidable : DecidableRel counterG.Adj := fun u v => by
  unfold counterG
  exact instDecidableAnd

private instance neighborSet_decidable (v : Fin 79) : DecidablePred (· ∈ counterG.neighborSet v) :=
  fun x => show Decidable (counterG.Adj v x) from inferInstance

private instance induce_decidable_rel {α : Type*} (s : Set α) (G : SimpleGraph α) [DecidableRel G.Adj] :
    DecidableRel (induce s G).Adj :=
  fun u v => show Decidable (G.Adj u.val v.val) from inferInstance


/-- Helper: adjacency in counterG. -/
private lemma counterG_adj (u v : Fin 79) : counterG.Adj u v ↔
    u ≠ v ∧ (
      ((u.val < 3 ∧ 3 ≤ v.val ∧ v.val < 6) ∨ (v.val < 3 ∧ 3 ≤ u.val ∧ u.val < 6))
      ∨ (6 ≤ u.val ∧ 6 ≤ v.val)
      ∨ (u.val = 0 ∧ 6 ≤ v.val)
      ∨ (v.val = 0 ∧ 6 ≤ u.val)
    ) := Iff.rfl

/-- Every vertex is reachable from vertex 0. -/
private lemma counterG_reachable_from_zero (v : Fin 79) : counterG.Reachable 0 v := by
  by_cases hv0 : v = 0
  · subst hv0; exact Reachable.refl _
  · rcases Nat.lt_or_ge v.val 6 with hlt6 | hge6
    · rcases Nat.lt_or_ge v.val 3 with hlt3 | hge3
      · -- v ∈ {1, 2}: 0 → 3 → v
        have h03 : counterG.Adj 0 (3 : Fin 79) := by
          constructor
          · intro h; simp at h
          · left; left; constructor <;> omega
        have h3v : counterG.Adj (3 : Fin 79) v := by
          constructor
          · intro h; have := Fin.val_eq_of_eq h; omega
          · left; right; constructor <;> omega
        exact h03.reachable.trans h3v.reachable
      · -- v ∈ {3, 4, 5}: 0 → v directly
        have h0v : counterG.Adj 0 v := by
          refine ⟨fun h => hv0 ?_, Or.inl (Or.inl ⟨by omega, by omega⟩)⟩
          exact Fin.ext (by have := Fin.val_eq_of_eq h; omega)
        exact h0v.reachable
    · -- v ∈ {6, ..., 78}: 0 → v via bridge
      have h0v : counterG.Adj 0 v := by
        refine ⟨fun h => hv0 ?_, Or.inr (Or.inr (Or.inl ⟨rfl, hge6⟩))⟩
        exact Fin.ext (by have := Fin.val_eq_of_eq h; omega)
      exact h0v.reachable

/-- The counterexample graph is connected. -/
private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_zero u).symm.trans (counterG_reachable_from_zero v)

/-- `b(counterG) ≥ 7`: The set {0,1,2,3,4,5,6} induces a bipartite subgraph. -/
private lemma counterG_b_ge : (7 : ℝ) ≤ counterG.b := by
  unfold b
  suffices h : 7 ≤ largestInducedBipartiteSubgraphSize counterG by exact_mod_cast h
  apply le_csSup
  · exact ⟨79, fun n ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
  · refine ⟨{0, 1, 2, 3, 4, 5, 6}, ?_, by decide⟩
    -- IsBipartite = Colorable 2 = Nonempty (Coloring (Fin 2))
    -- Helper: membership in {0,...,6} implies val ≤ 6
    have mem_le : ∀ (w : Fin 79), w ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 79)) → w.val ≤ 6 := by
      decide
    refine ⟨SimpleGraph.Coloring.mk (fun ⟨v, _⟩ => if v.val < 3 then 0 else 1) ?_⟩
    intro ⟨u, hu⟩ ⟨v, hv⟩ hadj
    have hadj' : counterG.Adj u v := hadj
    rw [counterG_adj] at hadj'
    have hu_le := mem_le u (Finset.mem_coe.mp hu)
    have hv_le := mem_le v (Finset.mem_coe.mp hv)
    have hne := hadj'.1
    have hcases := hadj'.2
    -- The adjacency conditions, combined with u.val ≤ 6 and v.val ≤ 6,
    -- guarantee that exactly one of u,v has val < 3 and the other has val ≥ 3.
    -- So the coloring assigns different values.
    simp only [ne_eq]
    -- We just need to show: (u.val < 3 ↔ ¬(v.val < 3))
    -- i.e., exactly one has val < 3
    intro h_eq
    -- h_eq says the colors are equal, derive a contradiction
    split_ifs at h_eq with hu3 hv3
    · -- Both < 3: check none of the adjacency conditions hold
      -- K_{3,3}: needs one < 3 AND other ≥ 3, impossible
      -- K_73: both ≥ 6, impossible with < 3
      -- Bridge: u.val = 0 and v.val ≥ 6, impossible
      omega
    · exact absurd h_eq (by decide)
    · exact absurd h_eq (by decide)
    · -- Both ≥ 3: K_{3,3} needs one < 3, impossible; K_73 needs both ≥ 6 but vals ≤ 6 and u ≠ v
      -- Bridge needs one val = 0 but both ≥ 3
      omega

/-- A general helper to construct a cycle of length 3 (triangle). -/
private lemma isCycle_triangle {α : Type*} {G : SimpleGraph α} {u v w : α}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u)
    (hne1 : u ≠ v) (hne2 : v ≠ w) (hne3 : w ≠ u) :
    ∃ (p : G.Walk u u), p.IsCycle := by
  let p : G.Walk u u := Walk.cons huv (Walk.cons hvw (Walk.cons hwu Walk.nil))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · exact Walk.IsPath.nil
      · simp [hne3]
    · simp [hne1.symm, hne2]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- A general helper to construct a cycle of length 4 (quadrilateral). -/
private lemma isCycle_quad {α : Type*} {G : SimpleGraph α} {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_cd : c ≠ d) (hne_da : d ≠ a)
    (hne_ac : a ≠ c) (hne_bd : b ≠ d) :
    ∃ (p : G.Walk a a), p.IsCycle := by
  let p : G.Walk a a := Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · rw [Walk.cons_isPath_iff]
        constructor
        · exact Walk.IsPath.nil
        · simp [hne_da]
      · simp [hne_cd, hne_ac.symm]
    · simp [hne_bc, hne_bd, hne_ab.symm]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- A helper lemma to extract 2 distinct elements from a set of cardinality ≥ 2. -/
private lemma exists_two_of_card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let s' := s.erase x
  have hs' : 1 ≤ s'.card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < s'.card)
  have hx_ne_y : x ≠ y := by
    intro heq
    subst heq
    exact Finset.notMem_erase x s hy
  have hy_in : y ∈ s := Finset.mem_of_mem_erase hy
  exact ⟨x, hx, y, hy_in, hx_ne_y⟩

/-- A helper lemma to extract 3 distinct elements from a set of cardinality ≥ 3. -/
private lemma exists_three_of_card_ge_three {α : Type*} [DecidableEq α] {s : Finset α} (h : 3 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ z ≠ x := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let s' := s.erase x
  have hs' : 2 ≤ s'.card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < s'.card)
  have hx_ne_y : x ≠ y := by
    intro heq
    subst heq
    exact Finset.notMem_erase x s hy
  have hy_in : y ∈ s := Finset.mem_of_mem_erase hy
  let s'' := s'.erase y
  have hs'' : 1 ≤ s''.card := by
    rw [Finset.card_erase_of_mem hy]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < s''.card)
  have hy_ne_z : y ≠ z := by
    intro heq
    subst heq
    exact Finset.notMem_erase y s' hz
  have hx_ne_z : x ≠ z := by
    intro heq
    subst heq
    have hz' := Finset.mem_of_mem_erase hz
    exact Finset.notMem_erase x s hz'
  have hz_in : z ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  exact ⟨x, hx, y, hy_in, z, hz_in, hx_ne_y, hy_ne_z, hx_ne_z.symm⟩

private lemma indepNum_le_one_of_clique {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hclique : ∀ u v : V, u ≠ v → G.Adj u v) :
    G.indepNum = 1 := by
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      simp [SimpleGraph.IsIndepSet]
    · rintro n ⟨s, hs, rfl⟩
      by_contra hgt
      push_neg at hgt
      have h_card : 2 ≤ s.card := by omega
      obtain ⟨x, hx, y, hy, hne⟩ := exists_two_of_card_ge_two h_card
      have h_indep : ¬G.Adj x y := hs (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) hne
      have h_adj : G.Adj x y := hclique x y hne
      exact h_indep h_adj
  · obtain ⟨v⟩ := ‹Nonempty V›
    apply le_csSup
    · exact ⟨Fintype.card V, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ⟩
    · refine ⟨{v}, ?_⟩
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hne
        simp only [coe_singleton, Set.mem_singleton_iff] at hx hy
        subst hx hy; exact absurd rfl hne
      · simp

private lemma counterG_indepNeighborsCard_1 : indepNeighborsCard counterG 1 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_2 : indepNeighborsCard counterG 2 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_3 : indepNeighborsCard counterG 3 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_4 : indepNeighborsCard counterG 4 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_5 : indepNeighborsCard counterG 5 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide


private lemma counterG_indepNeighborsCard_ge6 (v : Fin 79) (hv : 6 ≤ v.val) :
    indepNeighborsCard counterG v = 1 := by
  unfold indepNeighborsCard
  have h0_mem : (0 : Fin 79) ∈ counterG.neighborSet v := by
    rw [mem_neighborSet, counterG_adj]
    refine ⟨by omega, Or.inr (Or.inr (Or.inr ⟨rfl, hv⟩))⟩
  haveI : Nonempty ↑(counterG.neighborSet v) := ⟨⟨0, h0_mem⟩⟩
  apply indepNum_le_one_of_clique
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hne
  rw [mem_neighborSet, counterG_adj] at hx hy
  have hx_val : x = 0 ∨ 6 ≤ x.val := by
    rcases hx.2 with ((h1 | h2) | h3 | h4 | h5)
    · omega
    · omega
    · right; exact h3.right
    · right; exact h4.right
    · left; exact Fin.ext h5.left
  have hy_val : y = 0 ∨ 6 ≤ y.val := by
    rcases hy.2 with ((h1 | h2) | h3 | h4 | h5)
    · omega
    · omega
    · right; exact h3.right
    · right; exact h4.right
    · left; exact Fin.ext h5.left
  have hne_val : x ≠ y := fun h => hne (Subtype.ext h)
  change counterG.Adj x y
  rw [counterG_adj]
  refine ⟨hne_val, ?_⟩
  rcases hx_val with rfl | hx6
  · rcases hy_val with rfl | hy6
    · exact absurd rfl hne_val
    · right; right; left; exact ⟨rfl, hy6⟩
  · rcases hy_val with rfl | hy6
    · right; right; right; exact ⟨rfl, hx6⟩
    · right; left; exact ⟨hx6, hy6⟩

private lemma counterG_indepNeighborsCard_zero : indepNeighborsCard counterG 0 = 4 := by
  unfold indepNeighborsCard
  have h3_in : (3 : Fin 79) ∈ counterG.neighborSet 0 := by
    rw [mem_neighborSet, counterG_adj]; refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
  have h4_in : (4 : Fin 79) ∈ counterG.neighborSet 0 := by
    rw [mem_neighborSet, counterG_adj]; refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
  have h5_in : (5 : Fin 79) ∈ counterG.neighborSet 0 := by
    rw [mem_neighborSet, counterG_adj]; refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
  have h6_in : (6 : Fin 79) ∈ counterG.neighborSet 0 := by
    rw [mem_neighborSet, counterG_adj]; refine ⟨by decide, Or.inr (Or.inr (Or.inl ⟨rfl, by decide⟩))⟩
  let w3 : Subtype (counterG.neighborSet 0) := ⟨3, h3_in⟩
  let w4 : Subtype (counterG.neighborSet 0) := ⟨4, h4_in⟩
  let w5 : Subtype (counterG.neighborSet 0) := ⟨5, h5_in⟩
  let w6 : Subtype (counterG.neighborSet 0) := ⟨6, h6_in⟩
  haveI : Nonempty ↑(counterG.neighborSet 0) := ⟨w3⟩
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      simp [SimpleGraph.IsIndepSet]
    · rintro n ⟨s, hs, rfl⟩
      let A := s.filter (fun x => x.val.val < 6)
      let B := s.filter (fun x => 6 ≤ x.val.val)
      have hs_partition : s.card = A.card + B.card := by
        have hAB : s = A ∪ B := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, A, B]
          constructor
          · intro h
            rcases Nat.lt_or_ge x.val.val 6 with hlt | hge
            · left; exact ⟨h, hlt⟩
            · right; exact ⟨h, hge⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          simp only [A, B, Finset.mem_filter] at hxA hxB
          omega
        rw [← Finset.card_union_of_disjoint hdisj, ← hAB]
      have hA_le : A.card ≤ 3 := by
        have hA_sub : A ⊆ {w3, w4, w5} := by
          intro w hw
          simp only [A, Finset.mem_filter] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have h_in := w.property
          rw [mem_neighborSet, counterG_adj] at h_in
          have h_lt6 : w.val.val < 6 := hw.2
          have hw_val : w.val = 3 ∨ w.val = 4 ∨ w.val = 5 := by
            rcases h_in.2 with ((h1 | h2) | h3 | h4 | h5)
            · omega
            · omega
            · omega
            · omega
            · omega
          rcases hw_val with h3 | h4 | h5
          · left; exact Subtype.ext h3
          · right; left; exact Subtype.ext h4
          · right; right; exact Subtype.ext h5
        have h_card3 : ({w3, w4, w5} : Finset (Subtype (counterG.neighborSet 0))).card ≤ 3 := by
          calc ({w3, w4, w5} : Finset _).card
            _ ≤ ({w4, w5} : Finset _).card + 1 := card_insert_le _ _
            _ ≤ ({w5} : Finset _).card + 1 + 1 := add_le_add_right (card_insert_le w4 {w5}) 1
            _ = 3 := by simp
        exact le_trans (Finset.card_le_card hA_sub) h_card3
      have hB_le : B.card ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        have hB2 : 2 ≤ B.card := hgt
        obtain ⟨x, hxB, y, hyB, hne⟩ := exists_two_of_card_ge_two hB2
        have hx_in : x ∈ s := Finset.mem_of_mem_filter x hxB
        have hy_in : y ∈ s := Finset.mem_of_mem_filter y hyB
        have hx6 : 6 ≤ x.val.val := (Finset.mem_filter.mp hxB).2
        have hy6 : 6 ≤ y.val.val := (Finset.mem_filter.mp hyB).2
        have hne_val : x.val ≠ y.val := fun h => hne (Subtype.ext h)
        have hadj : counterG.Adj x.val y.val := by
          rw [counterG_adj]
          refine ⟨hne_val, Or.inr (Or.inl ⟨hx6, hy6⟩)⟩
        have hindep : ¬(counterG.induce (counterG.neighborSet 0)).Adj x y :=
          hs (Finset.mem_coe.mp hx_in) (Finset.mem_coe.mp hy_in) hne
        have : (counterG.induce (counterG.neighborSet 0)).Adj x y := hadj
        exact hindep this
      omega
  · apply le_csSup
    · exact ⟨79, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ.trans (by decide)⟩
    · refine ⟨{w3, w4, w5, w6}, ?_⟩
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hne
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        have hne_val : x.val ≠ y.val := fun h => hne (Subtype.ext h)
        change ¬counterG.Adj x.val y.val
        rw [counterG_adj]
        intro h_adj
        have h_cases : (x.val = 3 ∨ x.val = 4 ∨ x.val = 5 ∨ x.val = 6) ∧ (y.val = 3 ∨ y.val = 4 ∨ y.val = 5 ∨ y.val = 6) := by
          refine ⟨?_, ?_⟩
          · rcases hx with rfl | rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; left; rfl
            · right; right; right; rfl
          · rcases hy with rfl | rfl | rfl | rfl
            · left; rfl
            · right; left; rfl
            · right; right; left; rfl
            · right; right; right; rfl
        rcases h_adj.2 with ((h1 | h2) | h3 | h4 | h5)
        · omega
        · omega
        · omega
        · omega
        · omega
      · have hw3 : w3 ∉ ({w4, w5, w6} : Finset _) := by
          simp only [mem_insert, mem_singleton]
          rintro (h | h | h) <;>
          · have h_val := congr_arg (fun x => x.val.val) h
            dsimp [w3, w4, w5, w6] at h_val
            omega
        have hw4 : w4 ∉ ({w5, w6} : Finset _) := by
          simp only [mem_insert, mem_singleton]
          rintro (h | h) <;>
          · have h_val := congr_arg (fun x => x.val.val) h
            dsimp [w3, w4, w5, w6] at h_val
            omega
        have hw5 : w5 ∉ ({w6} : Finset _) := by
          simp only [mem_singleton]
          intro h
          have h_val := congr_arg (fun x => x.val.val) h
          dsimp [w3, w4, w5, w6] at h_val
          omega
        simp [hw3, hw4, hw5]


private lemma sum_univ_partition (f : Fin 79 → ℕ) :
    (∑ v : Fin 79, f v) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + ∑ v ∈ (univ.filter (fun (v : Fin 79) => 6 ≤ v.val)), f v := by
  have h_union : (univ : Finset (Fin 79)) = {0, 1, 2, 3, 4, 5} ∪ (univ.filter (fun (v : Fin 79) => 6 ≤ v.val)) := by
    ext x
    simp only [mem_univ, mem_union, mem_insert, mem_singleton, mem_filter, true_and, true_iff]
    rcases Nat.lt_or_ge x.val 6 with hlt | hge
    · left
      interval_cases h : x.val
      · have : x = 0 := Fin.ext h
        subst this; simp
      · have : x = 1 := Fin.ext h
        subst this; simp
      · have : x = 2 := Fin.ext h
        subst this; simp
      · have : x = 3 := Fin.ext h
        subst this; simp
      · have : x = 4 := Fin.ext h
        subst this; simp
      · have : x = 5 := Fin.ext h
        subst this; simp
    · right; exact hge
  have h_disj : Disjoint ({0, 1, 2, 3, 4, 5} : Finset (Fin 79)) (univ.filter (fun (v : Fin 79) => 6 ≤ v.val)) := by
    decide
  nth_rw 1 [h_union]
  rw [sum_union h_disj]
  simp [sum_insert]
  omega

/-- `l_avg(counterG) = 92/79` -/
private lemma counterG_l_avg : counterG.l_avg = 92 / 79 := by
  unfold l_avg averageIndepNeighbors indepNeighbors
  suffices h_sum : (∑ v : Fin 79, (indepNeighborsCard counterG v : ℝ)) = 92 by
    rw [h_sum]
    simp
  have h_sum_nat : (∑ v : Fin 79, indepNeighborsCard counterG v) = 92 := by
    rw [sum_univ_partition (indepNeighborsCard counterG)]
    rw [counterG_indepNeighborsCard_zero]
    rw [counterG_indepNeighborsCard_1]
    rw [counterG_indepNeighborsCard_2]
    rw [counterG_indepNeighborsCard_3]
    rw [counterG_indepNeighborsCard_4]
    rw [counterG_indepNeighborsCard_5]
    have h_filter : (∑ v ∈ univ.filter (fun (v : Fin 79) => 6 ≤ v.val), indepNeighborsCard counterG v) =
        ∑ v ∈ univ.filter (fun (v : Fin 79) => 6 ≤ v.val), 1 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      exact counterG_indepNeighborsCard_ge6 v hv
    rw [h_filter]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    have h_card : (univ.filter (fun (v : Fin 79) => 6 ≤ v.val)).card = 73 := by
      decide
    rw [h_card]
  exact_mod_cast h_sum_nat

/-- `f(counterG) ≤ 6`: Any induced subgraph with ≥ 7 vertices has a cycle. -/
private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 6 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩; simp at hv
  · intro n ⟨s, hacyclic, hcard⟩
    by_contra hgt; push_neg at hgt; rw [← hcard] at hgt
    let A := s.filter (fun v => 6 ≤ v.val)
    let B := s.filter (fun v => v.val < 6)
    have hs_partition : s.card = A.card + B.card := by
      have hAB : s = A ∪ B := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, A, B]
        constructor
        · intro h
          rcases Nat.lt_or_ge x.val 6 with hlt | hge
          · right; exact ⟨h, hlt⟩
          · left; exact ⟨h, hge⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        simp only [A, B, Finset.mem_filter] at hxA hxB
        omega
      rw [← Finset.card_union_of_disjoint hdisj, ← hAB]
    rcases Nat.lt_or_ge A.card 3 with hAlt3 | hAge3
    · -- A.card < 3
      interval_cases hA : A.card
      · -- A.card = 0
        have hB_le : B.card ≤ 6 := by
          have hB_sub : B ⊆ {0, 1, 2, 3, 4, 5} := by
            intro w hw
            simp only [B, Finset.mem_filter] at hw
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have : w.val < 6 := hw.2
            rcases w with ⟨val, h_lt⟩
            dsimp at this ⊢
            omega
          exact le_trans (Finset.card_le_card hB_sub) (by decide)
        omega
      · -- A.card = 1
        have hB_eq : B = {0, 1, 2, 3, 4, 5} := by
          have hB_sub : B ⊆ {0, 1, 2, 3, 4, 5} := by
            intro w hw
            simp only [B, Finset.mem_filter] at hw
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have : w.val < 6 := hw.2
            rcases w with ⟨val, h_lt⟩
            dsimp at this ⊢
            omega
          have hB_le : B.card ≤ 6 := by
            exact le_trans (Finset.card_le_card hB_sub) (by decide)
          have hB_card : B.card = 6 := le_antisymm hB_le (by omega)
          exact Finset.eq_of_subset_of_card_le hB_sub (by simp [hB_card])
        have h1_in : (1 : Fin 79) ∈ s := by
          have h : 1 ∈ B := by rw [hB_eq]; decide
          exact (Finset.mem_filter.mp h).1
        have h3_in : (3 : Fin 79) ∈ s := by
          have h : 3 ∈ B := by rw [hB_eq]; decide
          exact (Finset.mem_filter.mp h).1
        have h2_in : (2 : Fin 79) ∈ s := by
          have h : 2 ∈ B := by rw [hB_eq]; decide
          exact (Finset.mem_filter.mp h).1
        have h4_in : (4 : Fin 79) ∈ s := by
          have h : 4 ∈ B := by rw [hB_eq]; decide
          exact (Finset.mem_filter.mp h).1
        have hab : counterG.Adj 1 3 := by
          rw [counterG_adj]
          refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
        have hbc : counterG.Adj 3 2 := by
          rw [counterG_adj]
          refine ⟨by decide, Or.inl (Or.inr ⟨by decide, by decide⟩)⟩
        have hcd : counterG.Adj 2 4 := by
          rw [counterG_adj]
          refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
        have hda : counterG.Adj 4 1 := by
          rw [counterG_adj]
          refine ⟨by decide, Or.inl (Or.inr ⟨by decide, by decide⟩)⟩
        let va : s := ⟨1, h1_in⟩
        let vb : s := ⟨3, h3_in⟩
        let vc : s := ⟨2, h2_in⟩
        let vd : s := ⟨4, h4_in⟩
        have h_adj_ab : (counterG.induce s).Adj va vb := hab
        have h_adj_bc : (counterG.induce s).Adj vb vc := hbc
        have h_adj_cd : (counterG.induce s).Adj vc vd := hcd
        have h_adj_da : (counterG.induce s).Adj vd va := hda
        have hne_ab : va ≠ vb := fun h => (by decide : (1 : Fin 79) ≠ 3) (Subtype.ext_iff.mp h)
        have hne_bc : vb ≠ vc := fun h => (by decide : (3 : Fin 79) ≠ 2) (Subtype.ext_iff.mp h)
        have hne_cd : vc ≠ vd := fun h => (by decide : (2 : Fin 79) ≠ 4) (Subtype.ext_iff.mp h)
        have hne_da : vd ≠ va := fun h => (by decide : (4 : Fin 79) ≠ 1) (Subtype.ext_iff.mp h)
        have hne_ac : va ≠ vc := fun h => (by decide : (1 : Fin 79) ≠ 2) (Subtype.ext_iff.mp h)
        have hne_bd : vb ≠ vd := fun h => (by decide : (3 : Fin 79) ≠ 4) (Subtype.ext_iff.mp h)
        obtain ⟨p, hp⟩ := isCycle_quad h_adj_ab h_adj_bc h_adj_cd h_adj_da hne_ab hne_bc hne_cd hne_da hne_ac hne_bd
        exact hacyclic p hp
      · -- A.card = 2
        have hB_sub : B ⊆ {0, 1, 2, 3, 4, 5} := by
          intro w hw
          simp only [B, Finset.mem_filter] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have : w.val < 6 := hw.2
          rcases w with ⟨val, h_lt⟩
          dsimp at this ⊢
          omega
        by_cases h0 : (0 : Fin 79) ∈ B
        · obtain ⟨x, hxA, y, hyA, hne_xy⟩ := exists_two_of_card_ge_two (by omega : 2 ≤ A.card)
          have h0_in : (0 : Fin 79) ∈ s := Finset.mem_of_mem_filter 0 h0
          have hx_in : x ∈ s := Finset.mem_of_mem_filter x hxA
          have hy_in : y ∈ s := Finset.mem_of_mem_filter y hyA
          have hx6 : 6 ≤ x.val := (Finset.mem_filter.mp hxA).2
          have hy6 : 6 ≤ y.val := (Finset.mem_filter.mp hyA).2
          have h0x : counterG.Adj 0 x := by
            rw [counterG_adj]
            have h0_ne_x : (0 : Fin 79) ≠ x := by
              intro h
              have h_val := congr_arg Fin.val h
              omega
            refine ⟨h0_ne_x, Or.inr (Or.inr (Or.inl ⟨rfl, hx6⟩))⟩
          have hxy : counterG.Adj x y := by
            rw [counterG_adj]
            refine ⟨hne_xy, Or.inr (Or.inl ⟨hx6, hy6⟩)⟩
          have hy0 : counterG.Adj y 0 := by
            rw [counterG_adj]
            have hy_ne_0 : y ≠ 0 := by
              intro h
              have h_val := congr_arg Fin.val h
              omega
            refine ⟨hy_ne_0, Or.inr (Or.inr (Or.inr ⟨rfl, hy6⟩))⟩
          let v0 : s := ⟨0, h0_in⟩
          let vx : s := ⟨x, hx_in⟩
          let vy : s := ⟨y, hy_in⟩
          have h_adj_0x : (counterG.induce s).Adj v0 vx := h0x
          have h_adj_xy : (counterG.induce s).Adj vx vy := hxy
          have h_adj_y0 : (counterG.induce s).Adj vy v0 := hy0
          have hne_0x : v0 ≠ vx := by
            intro heq
            have h_eq' : (0 : Fin 79) = x := Subtype.ext_iff.mp heq
            have h_val := congr_arg Fin.val h_eq'
            omega
          have hne_xy' : vx ≠ vy := fun h => hne_xy (Subtype.ext_iff.mp h)
          have hne_y0 : vy ≠ v0 := by
            intro heq
            have h_eq' : y = 0 := Subtype.ext_iff.mp heq
            have h_val := congr_arg Fin.val h_eq'
            omega
          obtain ⟨p, hp⟩ := isCycle_triangle h_adj_0x h_adj_xy h_adj_y0 hne_0x hne_xy' hne_y0
          exact hacyclic p hp
        · have hB_eq : B = {1, 2, 3, 4, 5} := by
            have hB_sub' : B ⊆ {1, 2, 3, 4, 5} := by
              intro w hw
              have h0_ne : w ≠ 0 := by
                intro heq
                subst heq
                exact h0 hw
              simp only [B, Finset.mem_filter] at hw
              simp only [Finset.mem_insert, Finset.mem_singleton]
              have : w.val < 6 := hw.2
              rcases w with ⟨val, h_lt⟩
              have : val ≠ 0 := by
                intro heq
                subst heq
                exact h0_ne rfl
              dsimp at this ⊢
              omega
            have hB_card5 : B.card ≤ 5 := by
              exact le_trans (Finset.card_le_card hB_sub') (by decide)
            have hB_card : B.card = 5 := by omega
            exact Finset.eq_of_subset_of_card_le hB_sub' (by simp [hB_card])
          have h1_in : (1 : Fin 79) ∈ s := by
            have h : 1 ∈ B := by rw [hB_eq]; decide
            exact (Finset.mem_filter.mp h).1
          have h3_in : (3 : Fin 79) ∈ s := by
            have h : 3 ∈ B := by rw [hB_eq]; decide
            exact (Finset.mem_filter.mp h).1
          have h2_in : (2 : Fin 79) ∈ s := by
            have h : 2 ∈ B := by rw [hB_eq]; decide
            exact (Finset.mem_filter.mp h).1
          have h4_in : (4 : Fin 79) ∈ s := by
            have h : 4 ∈ B := by rw [hB_eq]; decide
            exact (Finset.mem_filter.mp h).1
          have hab : counterG.Adj 1 3 := by
            rw [counterG_adj]
            refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
          have hbc : counterG.Adj 3 2 := by
            rw [counterG_adj]
            refine ⟨by decide, Or.inl (Or.inr ⟨by decide, by decide⟩)⟩
          have hcd : counterG.Adj 2 4 := by
            rw [counterG_adj]
            refine ⟨by decide, Or.inl (Or.inl ⟨by decide, by decide⟩)⟩
          have hda : counterG.Adj 4 1 := by
            rw [counterG_adj]
            refine ⟨by decide, Or.inl (Or.inr ⟨by decide, by decide⟩)⟩
          let va : s := ⟨1, h1_in⟩
          let vb : s := ⟨3, h3_in⟩
          let vc : s := ⟨2, h2_in⟩
          let vd : s := ⟨4, h4_in⟩
          have h_adj_ab : (counterG.induce s).Adj va vb := hab
          have h_adj_bc : (counterG.induce s).Adj vb vc := hbc
          have h_adj_cd : (counterG.induce s).Adj vc vd := hcd
          have h_adj_da : (counterG.induce s).Adj vd va := hda
          have hne_ab : va ≠ vb := fun h => (by decide : (1 : Fin 79) ≠ 3) (Subtype.ext_iff.mp h)
          have hne_bc : vb ≠ vc := fun h => (by decide : (3 : Fin 79) ≠ 2) (Subtype.ext_iff.mp h)
          have hne_cd : vc ≠ vd := fun h => (by decide : (2 : Fin 79) ≠ 4) (Subtype.ext_iff.mp h)
          have hne_da : vd ≠ va := fun h => (by decide : (4 : Fin 79) ≠ 1) (Subtype.ext_iff.mp h)
          have hne_ac : va ≠ vc := fun h => (by decide : (1 : Fin 79) ≠ 2) (Subtype.ext_iff.mp h)
          have hne_bd : vb ≠ vd := fun h => (by decide : (3 : Fin 79) ≠ 4) (Subtype.ext_iff.mp h)
          obtain ⟨p, hp⟩ := isCycle_quad h_adj_ab h_adj_bc h_adj_cd h_adj_da hne_ab hne_bc hne_cd hne_da hne_ac hne_bd
          exact hacyclic p hp
    · obtain ⟨x, hxA, y, hyA, z, hzA, hne_xy, hne_yz, hne_zx⟩ :=
        exists_three_of_card_ge_three hAge3
      have hx_in : x ∈ s := Finset.mem_of_mem_filter x hxA
      have hy_in : y ∈ s := Finset.mem_of_mem_filter y hyA
      have hz_in : z ∈ s := Finset.mem_of_mem_filter z hzA
      have hx6 : 6 ≤ x.val := (Finset.mem_filter.mp hxA).2
      have hy6 : 6 ≤ y.val := (Finset.mem_filter.mp hyA).2
      have hz6 : 6 ≤ z.val := (Finset.mem_filter.mp hzA).2
      have h_adj_xy : counterG.Adj x y := by
        rw [counterG_adj]
        refine ⟨hne_xy, Or.inr (Or.inl ⟨hx6, hy6⟩)⟩
      have h_adj_yz : counterG.Adj y z := by
        rw [counterG_adj]
        refine ⟨hne_yz, Or.inr (Or.inl ⟨hy6, hz6⟩)⟩
      have h_adj_zx : counterG.Adj z x := by
        rw [counterG_adj]
        refine ⟨hne_zx, Or.inr (Or.inl ⟨hz6, hx6⟩)⟩
      let vx : s := ⟨x, hx_in⟩
      let vy : s := ⟨y, hy_in⟩
      let vz : s := ⟨z, hz_in⟩
      have h_adj_v_xy : (counterG.induce s).Adj vx vy := h_adj_xy
      have h_adj_v_yz : (counterG.induce s).Adj vy vz := h_adj_yz
      have h_adj_v_zx : (counterG.induce s).Adj vz vx := h_adj_zx
      have hne_v_xy : vx ≠ vy := fun h => hne_xy (Subtype.ext_iff.mp h)
      have hne_v_yz : vy ≠ vz := fun h => hne_yz (Subtype.ext_iff.mp h)
      have hne_v_zx : vz ≠ vx := fun h => hne_zx (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ := isCycle_triangle h_adj_v_xy h_adj_v_yz h_adj_v_zx hne_v_xy hne_v_yz hne_v_zx
      exact hacyclic p hp

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true

/--
WOWII [Conjecture 58](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.

This conjecture is false. A counterexample is the graph described in the module docstring
above: a $K_{3,3}$ joined to a $K_{73}$ via vertex $0$, giving
$\lceil b/l_{\mathrm{avg}} \rceil \ge 7 > 6 \ge f(G)$.
-/
@[category research solved, AMS 5]
theorem conjecture58 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      Nat.ceil (G.b / G.l_avg) ≤ G.largestInducedForestSize := by
  constructor
  · intro h; exact h.elim
  · intro hP
    -- Derive a contradiction from the counterexample on Fin 79
    -- First, extract the inequality for our concrete graph
    have hf := counterG_forest_le
    have hb := counterG_b_ge
    have hl := counterG_l_avg
    have hconn := counterG_connected
    -- The universal statement applied to Fin 79 gives us:
    -- ⌈counterG.b / counterG.l_avg⌉ ≤ counterG.largestInducedForestSize
    -- We show this leads to a contradiction.
    suffices h : ¬(Nat.ceil (counterG.b / counterG.l_avg) ≤ counterG.largestInducedForestSize) by
      exact h (hP (Fin 79) counterG hconn)
    rw [hl, not_le]
    -- Need: counterG.largestInducedForestSize < Nat.ceil (counterG.b / (92 / 79))
    -- i.e., 6 < ⌈counterG.b / (92/79)⌉
    calc counterG.largestInducedForestSize
        ≤ 6 := hf
      _ < Nat.ceil (counterG.b / (92 / 79)) := by
          rw [Nat.lt_ceil]; push_cast
          calc (6 : ℝ) < 553 / 92 := by norm_num
            _ = 7 * 79 / 92 := by ring
            _ ≤ counterG.b * 79 / 92 := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right hb (by positivity)
            _ = counterG.b / (92 / 79) := by ring

end WrittenOnTheWallII.GraphConjecture58
