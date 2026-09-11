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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 58 (smaller counterexample)

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

WOWII Conjecture 58 states that for a simple connected graph `G`,
`f(G) ≥ ⌈ b(G) / (average of l(v)) ⌉`, where `f(G)` is the forest number (largest
induced forest), `b(G)` is the bipartite number (largest induced bipartite subgraph),
and `l(v)` is the independence number of the neighborhood of `v`.

## Counterexample

The conjecture is false. This file records a *small* counterexample:

    G = C₄ —bridge— K₂₇

that is, a 4-cycle on `{0,1,2,3}` and a complete graph `K₂₇` on `{4,…,30}`, joined by a
single bridge edge `{0,4}`. This graph has `n = 31` vertices and satisfies:

- `b(G) ≥ 6`: the set `{0,1,2,3,5,6}` induces a bipartite subgraph (C₄ plus a disjoint edge).
- `f(G) ≤ 5`: the largest induced forest has at most 5 vertices (at most 3 of `{0,1,2,3}`
  and at most 2 of the clique).
- `l_avg(G) = 37/31`.
- `⌈ b(G) / l_avg(G) ⌉ ≥ ⌈ 6 / (37/31) ⌉ = ⌈186/37⌉ = 6 > 5 ≥ f(G)`.

This is the same refutation mechanism as the previously recorded counterexample
(`K₃,₃` joined to `K₇₃`, `n = 79`), but on far fewer vertices. Because the join here is a
single *bridge* edge (a cut edge), the only cycles of `G` are the 4-cycle `0-1-2-3` and the
triangles inside the clique, which makes the forest bound especially clean.
-/

namespace WrittenOnTheWallII.GraphConjecture58

open SimpleGraph Finset

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

/-- The counterexample graph on `Fin 31`:
- C₄: 4-cycle on `{0,1,2,3}` (`u,v < 4` adjacent iff `u + v` is odd),
- K₂₇: complete graph on `{4,…,30}`,
- bridge: the single edge `{0,4}`. -/
private def counterG : SimpleGraph (Fin 31) where
  Adj u v :=
    u ≠ v ∧ (
      -- C₄ edges on {0,1,2,3}: both < 4 and val-sum odd
      (u.val < 4 ∧ v.val < 4 ∧ (u.val + v.val) % 2 = 1)
      -- K₂₇ edges: both vertices in {4,...,30}
      ∨ (4 ≤ u.val ∧ 4 ≤ v.val)
      -- Bridge edge: {0,4}
      ∨ (u.val = 0 ∧ v.val = 4)
      ∨ (v.val = 0 ∧ u.val = 4)
    )
  symm u v h := by
    obtain ⟨hne, hcases⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases hcases with ⟨ha, hb, hc⟩ | h2 | h3 | h4
    · exact Or.inl ⟨hb, ha, by omega⟩
    · exact Or.inr (Or.inl ⟨h2.2, h2.1⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h3.1, h3.2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h4.1, h4.2⟩))
  loopless u h := h.1 rfl

private instance counterG_decidable : DecidableRel counterG.Adj := fun u v => by
  unfold counterG
  exact instDecidableAnd

private instance neighborSet_decidable (v : Fin 31) : DecidablePred (· ∈ counterG.neighborSet v) :=
  fun x => show Decidable (counterG.Adj v x) from inferInstance

private instance induce_decidable_rel {α : Type*} (s : Set α) (G : SimpleGraph α) [DecidableRel G.Adj] :
    DecidableRel (induce s G).Adj :=
  fun u v => show Decidable (G.Adj u.val v.val) from inferInstance

/-- Helper: adjacency in `counterG`. -/
private lemma counterG_adj (u v : Fin 31) : counterG.Adj u v ↔
    u ≠ v ∧ (
      (u.val < 4 ∧ v.val < 4 ∧ (u.val + v.val) % 2 = 1)
      ∨ (4 ≤ u.val ∧ 4 ≤ v.val)
      ∨ (u.val = 0 ∧ v.val = 4)
      ∨ (v.val = 0 ∧ u.val = 4)
    ) := Iff.rfl

/-- Every vertex is reachable from vertex `0`. -/
private lemma counterG_reachable_from_zero (v : Fin 31) : counterG.Reachable 0 v := by
  by_cases hv0 : v = 0
  · subst hv0; exact Reachable.refl _
  · rcases Nat.lt_or_ge v.val 4 with hlt4 | hge4
    · -- v ∈ {1, 2, 3}: 0 → 1 → v, or 0 → 1 directly. Use 0-1 and 1-v where possible.
      -- 0 is adjacent to 1 and 3 (odd sum). For v = 2, go 0 → 1 → 2.
      have h01 : counterG.Adj (0 : Fin 31) 1 := by
        refine ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      have h03 : counterG.Adj (0 : Fin 31) 3 := by
        refine ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      interval_cases h : v.val
      · exact absurd (Fin.ext h) hv0
      · have : v = 1 := Fin.ext h; subst this; exact h01.reachable
      · -- v = 2: 0 → 1 → 2
        have : v = 2 := Fin.ext h; subst this
        have h12 : counterG.Adj (1 : Fin 31) 2 := by
          refine ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
        exact h01.reachable.trans h12.reachable
      · have : v = 3 := Fin.ext h; subst this; exact h03.reachable
    · -- v ∈ {4, ..., 30}: 0 → 4 → v via bridge then clique
      have h04 : counterG.Adj (0 : Fin 31) 4 := by
        refine ⟨by decide, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      by_cases hv4 : v.val = 4
      · have : v = 4 := Fin.ext hv4; subst this; exact h04.reachable
      · have h4v : counterG.Adj (4 : Fin 31) v := by
          refine ⟨fun h => hv4 ?_, Or.inr (Or.inl ⟨by decide, hge4⟩)⟩
          exact (Fin.val_eq_of_eq h).symm
        exact h04.reachable.trans h4v.reachable

/-- The counterexample graph is connected. -/
private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_zero u).symm.trans (counterG_reachable_from_zero v)

/-- `b(counterG) ≥ 6`: the set `{0,1,2,3,5,6}` induces a bipartite subgraph.
The 2-coloring is by parity of the vertex value; every edge inside this set (the four
`C₄` edges and the single clique edge `5-6`) joins vertices of opposite parity, and the
bridge endpoint `4` is excluded so no bridge edge appears. -/
private lemma counterG_b_ge : (6 : ℝ) ≤ counterG.b := by
  unfold b
  suffices h : 6 ≤ largestInducedBipartiteSubgraphSize counterG by exact_mod_cast h
  apply le_csSup
  · exact ⟨31, fun n ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
  · refine ⟨{0, 1, 2, 3, 5, 6}, ?_, by decide⟩
    rw [induce_isBipartite_iff_exists_coloring]
    refine ⟨fun v => (⟨v.val % 2, by omega⟩ : Fin 2), ?_⟩
    have mem_vals : ∀ (w : Fin 31), w ∈ ({0, 1, 2, 3, 5, 6} : Finset (Fin 31)) →
        w.val = 0 ∨ w.val = 1 ∨ w.val = 2 ∨ w.val = 3 ∨ w.val = 5 ∨ w.val = 6 := by decide
    intro u hu v hv hadj
    have hu_val := mem_vals u hu
    have hv_val := mem_vals v hv
    rw [counterG_adj] at hadj
    intro heq
    have heq' : u.val % 2 = v.val % 2 := by
      have := Fin.mk.inj_iff.mp heq
      exact this
    rcases hadj.2 with ⟨_, _, hodd⟩ | ⟨hu4, hv4⟩ | ⟨h0, h4⟩ | ⟨h0, h4⟩ <;> omega

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
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < s'.card)
  have hx_ne_y : x ≠ y := by
    intro heq; subst heq; exact Finset.notMem_erase x s hy
  have hy_in : y ∈ s := Finset.mem_of_mem_erase hy
  exact ⟨x, hx, y, hy_in, hx_ne_y⟩

/-- A helper lemma to extract 3 distinct elements from a set of cardinality ≥ 3. -/
private lemma exists_three_of_card_ge_three {α : Type*} [DecidableEq α] {s : Finset α} (h : 3 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ z ≠ x := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let s' := s.erase x
  have hs' : 2 ≤ s'.card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < s'.card)
  have hx_ne_y : x ≠ y := by
    intro heq; subst heq; exact Finset.notMem_erase x s hy
  have hy_in : y ∈ s := Finset.mem_of_mem_erase hy
  let s'' := s'.erase y
  have hs'' : 1 ≤ s''.card := by
    rw [Finset.card_erase_of_mem hy]; omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < s''.card)
  have hy_ne_z : y ≠ z := by
    intro heq; subst heq; exact Finset.notMem_erase y s' hz
  have hx_ne_z : x ≠ z := by
    intro heq; subst heq
    have hz' := Finset.mem_of_mem_erase hz
    exact Finset.notMem_erase x s hz'
  have hz_in : z ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  exact ⟨x, hx, y, hy_in, z, hz_in, hx_ne_y, hy_ne_z, hx_ne_z.symm⟩

/-- The independence number of a clique is `1` (for a nonempty clique). -/
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
      exact h_indep (hclique x y hne)
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

private lemma counterG_indepNeighborsCard_0 : indepNeighborsCard counterG 0 = 3 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_1 : indepNeighborsCard counterG 1 = 2 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_2 : indepNeighborsCard counterG 2 = 2 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

private lemma counterG_indepNeighborsCard_3 : indepNeighborsCard counterG 3 = 2 := by
  unfold indepNeighborsCard
  rw [indep_num_eq_computable]
  decide

/-- For a clique vertex other than the bridge endpoint (`v ≥ 5`), the neighborhood is a clique,
so its local independence number is `1`. -/
private lemma counterG_indepNeighborsCard_ge5 (v : Fin 31) (hv : 5 ≤ v.val) :
    indepNeighborsCard counterG v = 1 := by
  unfold indepNeighborsCard
  have h4_mem : (4 : Fin 31) ∈ counterG.neighborSet v := by
    rw [mem_neighborSet, counterG_adj]
    refine ⟨by omega, Or.inr (Or.inl ⟨by omega, by decide⟩)⟩
  haveI : Nonempty ↑(counterG.neighborSet v) := ⟨⟨4, h4_mem⟩⟩
  apply indepNum_le_one_of_clique
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hne
  rw [mem_neighborSet, counterG_adj] at hx hy
  -- neighbors of v (v ≥ 5) all have value ≥ 4
  have hx4 : 4 ≤ x.val := by
    rcases hx.2 with ⟨h1, _, _⟩ | h2 | h3 | h4
    · omega
    · exact h2.2
    · omega
    · omega
  have hy4 : 4 ≤ y.val := by
    rcases hy.2 with ⟨h1, _, _⟩ | h2 | h3 | h4
    · omega
    · exact h2.2
    · omega
    · omega
  have hne_val : x ≠ y := fun h => hne (Subtype.ext h)
  change counterG.Adj x y
  rw [counterG_adj]
  exact ⟨hne_val, Or.inr (Or.inl ⟨hx4, hy4⟩)⟩

/-- The bridge endpoint `4` in the clique: its neighborhood is `{0} ∪ {5,…,30}`, a clique
plus the single isolated vertex `0`, so its local independence number is `2`. -/
private lemma counterG_indepNeighborsCard_4 : indepNeighborsCard counterG 4 = 2 := by
  unfold indepNeighborsCard
  have h0_in : (0 : Fin 31) ∈ counterG.neighborSet 4 := by
    rw [mem_neighborSet, counterG_adj]
    refine ⟨by decide, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have h5_in : (5 : Fin 31) ∈ counterG.neighborSet 4 := by
    rw [mem_neighborSet, counterG_adj]
    refine ⟨by decide, Or.inr (Or.inl ⟨by decide, by decide⟩)⟩
  let w0 : Subtype (counterG.neighborSet 4) := ⟨0, h0_in⟩
  let w5 : Subtype (counterG.neighborSet 4) := ⟨5, h5_in⟩
  haveI : Nonempty ↑(counterG.neighborSet 4) := ⟨w0⟩
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      simp [SimpleGraph.IsIndepSet]
    · rintro n ⟨s, hs, rfl⟩
      let A := s.filter (fun x => x.val.val = 0)
      let B := s.filter (fun x => 5 ≤ x.val.val)
      have hs_partition : s.card = A.card + B.card := by
        have hAB : s = A ∪ B := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, A, B]
          constructor
          · intro h
            -- every neighbor of 4 has value 0 or ≥ 5
            have hval := x.property
            rw [mem_neighborSet, counterG_adj] at hval
            have : x.val.val = 0 ∨ 5 ≤ x.val.val := by
              rcases hval.2 with ⟨h1, _, _⟩ | h2 | h3 | h4
              · omega
              · -- 4 ≤ x.val, and x ≠ 4 in neighborSet; but need ≥5. x.val could be 4? no: Adj 4 x needs x≠4
                have hne4 : x.val.val ≠ 4 := by
                  intro he
                  exact hval.1 (by rw [Fin.ext_iff]; omega)
                omega
              · omega
              · omega
            rcases this with h0 | h5
            · left; exact ⟨h, h0⟩
            · right; exact ⟨h, h5⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          simp only [A, B, Finset.mem_filter] at hxA hxB
          omega
        rw [← Finset.card_union_of_disjoint hdisj, ← hAB]
      have hA_le : A.card ≤ 1 := by
        rcases Nat.lt_or_ge A.card 2 with h | h
        · omega
        · exfalso
          obtain ⟨x, hxA, y, hyA, hne⟩ := exists_two_of_card_ge_two h
          have hx0 : x.val.val = 0 := (Finset.mem_filter.mp hxA).2
          have hy0 : y.val.val = 0 := (Finset.mem_filter.mp hyA).2
          exact hne (Subtype.ext (Fin.ext (by omega)))
      have hB_le : B.card ≤ 1 := by
        rcases Nat.lt_or_ge B.card 2 with h | h
        · omega
        · exfalso
          obtain ⟨x, hxB, y, hyB, hne⟩ := exists_two_of_card_ge_two h
          have hx_in : x ∈ s := Finset.mem_of_mem_filter x hxB
          have hy_in : y ∈ s := Finset.mem_of_mem_filter y hyB
          have hx5 : 5 ≤ x.val.val := (Finset.mem_filter.mp hxB).2
          have hy5 : 5 ≤ y.val.val := (Finset.mem_filter.mp hyB).2
          have hne_val : x.val ≠ y.val := fun h => hne (Subtype.ext h)
          have hadj : counterG.Adj x.val y.val := by
            rw [counterG_adj]
            exact ⟨hne_val, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
          have hindep : ¬(counterG.induce (counterG.neighborSet 4)).Adj x y :=
            hs (Finset.mem_coe.mp hx_in) (Finset.mem_coe.mp hy_in) hne
          exact hindep hadj
      omega
  · apply le_csSup
    · exact ⟨31, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ.trans (by decide)⟩
    · refine ⟨{w0, w5}, ?_⟩
      rw [isNIndepSet_iff]
      constructor
      · intro x hx y hy hne
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        have hne_val : x.val ≠ y.val := fun h => hne (Subtype.ext h)
        change ¬counterG.Adj x.val y.val
        rw [counterG_adj]
        rintro ⟨-, hcases⟩
        -- x, y ∈ {0, 5}; 0 and 5 are non-adjacent
        have hxv : x.val.val = 0 ∨ x.val.val = 5 := by
          rcases hx with rfl | rfl
          · left; rfl
          · right; rfl
        have hyv : y.val.val = 0 ∨ y.val.val = 5 := by
          rcases hy with rfl | rfl
          · left; rfl
          · right; rfl
        rcases hcases with ⟨h1, _, _⟩ | ⟨h2a, h2b⟩ | ⟨h3, _⟩ | ⟨h4, _⟩ <;> omega
      · have hw0 : w0 ∉ ({w5} : Finset _) := by
          simp only [mem_singleton]
          intro h
          have h_val := congr_arg (fun x => x.val.val) h
          dsimp [w0, w5] at h_val
          omega
        simp [hw0]

/-- Splitting `univ` for the local-independence sum: `{0,1,2,3,4}` and `{v | 5 ≤ v.val}`. -/
private lemma sum_univ_partition (f : Fin 31 → ℕ) :
    (∑ v : Fin 31, f v) = f 0 + f 1 + f 2 + f 3 + f 4
      + ∑ v ∈ (univ.filter (fun (v : Fin 31) => 5 ≤ v.val)), f v := by
  have h_union : (univ : Finset (Fin 31)) =
      {0, 1, 2, 3, 4} ∪ (univ.filter (fun (v : Fin 31) => 5 ≤ v.val)) := by
    ext x
    simp only [mem_univ, mem_union, mem_insert, mem_singleton, mem_filter, true_and, true_iff]
    rcases Nat.lt_or_ge x.val 5 with hlt | hge
    · left
      interval_cases h : x.val
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
    · right; exact hge
  have h_disj : Disjoint ({0, 1, 2, 3, 4} : Finset (Fin 31))
      (univ.filter (fun (v : Fin 31) => 5 ≤ v.val)) := by decide
  nth_rw 1 [h_union]
  rw [sum_union h_disj]
  simp [sum_insert]
  omega

/-- `l_avg(counterG) = 37/31`. -/
private lemma counterG_l_avg : counterG.l_avg = 37 / 31 := by
  unfold l_avg averageIndepNeighbors indepNeighbors
  suffices h_sum : (∑ v : Fin 31, (indepNeighborsCard counterG v : ℝ)) = 37 by
    rw [h_sum]; simp
  have h_sum_nat : (∑ v : Fin 31, indepNeighborsCard counterG v) = 37 := by
    rw [sum_univ_partition (indepNeighborsCard counterG)]
    rw [counterG_indepNeighborsCard_0, counterG_indepNeighborsCard_1,
        counterG_indepNeighborsCard_2, counterG_indepNeighborsCard_3,
        counterG_indepNeighborsCard_4]
    have h_filter : (∑ v ∈ univ.filter (fun (v : Fin 31) => 5 ≤ v.val), indepNeighborsCard counterG v)
        = ∑ v ∈ univ.filter (fun (v : Fin 31) => 5 ≤ v.val), 1 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      exact counterG_indepNeighborsCard_ge5 v hv
    rw [h_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h_card : (univ.filter (fun (v : Fin 31) => 5 ≤ v.val)).card = 26 := by decide
    rw [h_card]
  exact_mod_cast h_sum_nat

/-- `f(counterG) ≤ 5`: any induced subgraph with ≥ 6 vertices contains a cycle. Because the
join is a single bridge edge, the only cycles are the 4-cycle `0-1-2-3` and clique triangles:
6 vertices force either ≥ 3 clique vertices (a triangle) or all of `{0,1,2,3}` (the 4-cycle). -/
private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 5 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩; simp at hv
  · intro n ⟨s, hacyclic, hcard⟩
    by_contra hgt; push_neg at hgt; rw [← hcard] at hgt
    let A := s.filter (fun v => 4 ≤ v.val)
    let B := s.filter (fun v => v.val < 4)
    have hs_partition : s.card = A.card + B.card := by
      have hAB : s = A ∪ B := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, A, B]
        constructor
        · intro h
          rcases Nat.lt_or_ge x.val 4 with hlt | hge
          · right; exact ⟨h, hlt⟩
          · left; exact ⟨h, hge⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        simp only [A, B, Finset.mem_filter] at hxA hxB
        omega
      rw [← Finset.card_union_of_disjoint hdisj, ← hAB]
    have hB_le : B.card ≤ 4 := by
      have hB_sub : B ⊆ {0, 1, 2, 3} := by
        intro w hw
        simp only [B, Finset.mem_filter] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have : w.val < 4 := hw.2
        rcases w with ⟨val, h_lt⟩
        dsimp at this ⊢
        omega
      exact le_trans (Finset.card_le_card hB_sub) (by decide)
    rcases Nat.lt_or_ge A.card 3 with hAlt3 | hAge3
    · -- A.card ≤ 2, so B.card ≥ 4, hence B = {0,1,2,3}: the 4-cycle
      have hB_ge : 4 ≤ B.card := by omega
      have hB_card : B.card = 4 := le_antisymm hB_le hB_ge
      have hB_eq : B = {0, 1, 2, 3} := by
        have hB_sub : B ⊆ {0, 1, 2, 3} := by
          intro w hw
          simp only [B, Finset.mem_filter] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have : w.val < 4 := hw.2
          rcases w with ⟨val, h_lt⟩
          dsimp at this ⊢
          omega
        exact Finset.eq_of_subset_of_card_le hB_sub (by simp [hB_card])
      have h0_in : (0 : Fin 31) ∈ s := by
        have h : 0 ∈ B := by rw [hB_eq]; decide
        exact (Finset.mem_filter.mp h).1
      have h1_in : (1 : Fin 31) ∈ s := by
        have h : 1 ∈ B := by rw [hB_eq]; decide
        exact (Finset.mem_filter.mp h).1
      have h2_in : (2 : Fin 31) ∈ s := by
        have h : 2 ∈ B := by rw [hB_eq]; decide
        exact (Finset.mem_filter.mp h).1
      have h3_in : (3 : Fin 31) ∈ s := by
        have h : 3 ∈ B := by rw [hB_eq]; decide
        exact (Finset.mem_filter.mp h).1
      have hab : counterG.Adj 0 1 := by
        rw [counterG_adj]; exact ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      have hbc : counterG.Adj 1 2 := by
        rw [counterG_adj]; exact ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      have hcd : counterG.Adj 2 3 := by
        rw [counterG_adj]; exact ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      have hda : counterG.Adj 3 0 := by
        rw [counterG_adj]; exact ⟨by decide, Or.inl ⟨by decide, by decide, by decide⟩⟩
      let va : s := ⟨0, h0_in⟩
      let vb : s := ⟨1, h1_in⟩
      let vc : s := ⟨2, h2_in⟩
      let vd : s := ⟨3, h3_in⟩
      have h_adj_ab : (counterG.induce s).Adj va vb := hab
      have h_adj_bc : (counterG.induce s).Adj vb vc := hbc
      have h_adj_cd : (counterG.induce s).Adj vc vd := hcd
      have h_adj_da : (counterG.induce s).Adj vd va := hda
      have hne_ab : va ≠ vb := fun h => (by decide : (0 : Fin 31) ≠ 1) (Subtype.ext_iff.mp h)
      have hne_bc : vb ≠ vc := fun h => (by decide : (1 : Fin 31) ≠ 2) (Subtype.ext_iff.mp h)
      have hne_cd : vc ≠ vd := fun h => (by decide : (2 : Fin 31) ≠ 3) (Subtype.ext_iff.mp h)
      have hne_da : vd ≠ va := fun h => (by decide : (3 : Fin 31) ≠ 0) (Subtype.ext_iff.mp h)
      have hne_ac : va ≠ vc := fun h => (by decide : (0 : Fin 31) ≠ 2) (Subtype.ext_iff.mp h)
      have hne_bd : vb ≠ vd := fun h => (by decide : (1 : Fin 31) ≠ 3) (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ := isCycle_quad h_adj_ab h_adj_bc h_adj_cd h_adj_da
        hne_ab hne_bc hne_cd hne_da hne_ac hne_bd
      exact hacyclic p hp
    · -- A.card ≥ 3: three clique vertices form a triangle
      obtain ⟨x, hxA, y, hyA, z, hzA, hne_xy, hne_yz, hne_zx⟩ :=
        exists_three_of_card_ge_three hAge3
      have hx_in : x ∈ s := Finset.mem_of_mem_filter x hxA
      have hy_in : y ∈ s := Finset.mem_of_mem_filter y hyA
      have hz_in : z ∈ s := Finset.mem_of_mem_filter z hzA
      have hx4 : 4 ≤ x.val := (Finset.mem_filter.mp hxA).2
      have hy4 : 4 ≤ y.val := (Finset.mem_filter.mp hyA).2
      have hz4 : 4 ≤ z.val := (Finset.mem_filter.mp hzA).2
      have h_adj_xy : counterG.Adj x y := by
        rw [counterG_adj]; exact ⟨hne_xy, Or.inr (Or.inl ⟨hx4, hy4⟩)⟩
      have h_adj_yz : counterG.Adj y z := by
        rw [counterG_adj]; exact ⟨hne_yz, Or.inr (Or.inl ⟨hy4, hz4⟩)⟩
      have h_adj_zx : counterG.Adj z x := by
        rw [counterG_adj]; exact ⟨hne_zx, Or.inr (Or.inl ⟨hz4, hx4⟩)⟩
      let vx : s := ⟨x, hx_in⟩
      let vy : s := ⟨y, hy_in⟩
      let vz : s := ⟨z, hz_in⟩
      have h_adj_v_xy : (counterG.induce s).Adj vx vy := h_adj_xy
      have h_adj_v_yz : (counterG.induce s).Adj vy vz := h_adj_yz
      have h_adj_v_zx : (counterG.induce s).Adj vz vx := h_adj_zx
      have hne_v_xy : vx ≠ vy := fun h => hne_xy (Subtype.ext_iff.mp h)
      have hne_v_yz : vy ≠ vz := fun h => hne_yz (Subtype.ext_iff.mp h)
      have hne_v_zx : vz ≠ vx := fun h => hne_zx (Subtype.ext_iff.mp h)
      obtain ⟨p, hp⟩ := isCycle_triangle h_adj_v_xy h_adj_v_yz h_adj_v_zx
        hne_v_xy hne_v_yz hne_v_zx
      exact hacyclic p hp

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true

/--
WOWII [Conjecture 58](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.

This conjecture is false. The graph `C₄ —bridge— K₂₇` on `Fin 31` (a 4-cycle on `{0,1,2,3}`
and a `K₂₇` on `{4,…,30}` joined by the single edge `{0,4}`) is a counterexample:
`b(G) ≥ 6`, `l_avg(G) = 37/31`, and `f(G) ≤ 5`, so
`⌈ b/l_avg ⌉ ≥ ⌈186/37⌉ = 6 > 5 ≥ f(G)`.
-/
@[category research solved, AMS 5]
theorem conjecture58 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      Nat.ceil (G.b / G.l_avg) ≤ G.largestInducedForestSize := by
  constructor
  · intro h; exact h.elim
  · intro hP
    have hf := counterG_forest_le
    have hb := counterG_b_ge
    have hl := counterG_l_avg
    have hconn := counterG_connected
    suffices h : ¬(Nat.ceil (counterG.b / counterG.l_avg) ≤ counterG.largestInducedForestSize) by
      exact h (hP (Fin 31) counterG hconn)
    rw [hl, not_le]
    calc counterG.largestInducedForestSize
        ≤ 5 := hf
      _ < Nat.ceil (counterG.b / (37 / 31)) := by
          rw [Nat.lt_ceil]; push_cast
          calc (5 : ℝ) < 186 / 37 := by norm_num
            _ = 6 * 31 / 37 := by ring
            _ ≤ counterG.b * 31 / 37 := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right hb (by positivity)
            _ = counterG.b / (37 / 31) := by ring

end WrittenOnTheWallII.GraphConjecture58
