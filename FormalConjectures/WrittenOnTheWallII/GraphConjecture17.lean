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
# Written on the Wall II - Conjecture 17

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false


namespace WrittenOnTheWallII.GraphConjecture17

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
lemma not_adj_of_shortest_walk {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h_dist : i + 2 ≤ j) : ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro h_adj
  let h_walk : G.Walk u v :=
    (p.take i).append ((Walk.cons h_adj Walk.nil).append (p.drop j))
  have h_len : h_walk.length = i + 1 + (p.length - j) := by
    dsimp [h_walk]
    simp
    omega
  have h_dist_le : G.dist u v ≤ h_walk.length := G.dist_le h_walk
  rw [h_len, ← hp] at h_dist_le
  omega

noncomputable def greedySeq (I : ℕ → Prop) : ℕ → ℕ
| 0 => if I 0 then 1 else 0
| k + 1 => if I (greedySeq I k + 2) then greedySeq I k + 3 else greedySeq I k + 2

lemma greedySeq_le (I : ℕ → Prop) (k : ℕ) : greedySeq I k ≤ 3 * k + 1 := by
  induction' k with k ih
  · simp [greedySeq]
    split <;> omega
  · simp [greedySeq]
    split <;> omega

lemma greedySeq_not_I (I : ℕ → Prop) (hI : ∀ n, I n → ¬ I (n + 1)) (k : ℕ) : ¬ I (greedySeq I k) := by
  cases k
  · simp [greedySeq]
    split
    · intro h; exact hI 0 ‹_› h
    · assumption
  · simp [greedySeq]
    split
    · intro h; exact hI _ ‹_› h
    · assumption

lemma greedySeq_strict_mono (I : ℕ → Prop) (k : ℕ) : greedySeq I k + 2 ≤ greedySeq I (k + 1) := by
  simp [greedySeq]
  split <;> omega

lemma greedySeq_mono_add (I : ℕ → Prop) (k m : ℕ) (h : k < m) : greedySeq I k + 2 ≤ greedySeq I m := by
  induction' m with m ih
  · omega
  · rcases eq_or_lt_of_le (Nat.le_of_lt_succ h) with rfl | h'
    · exact greedySeq_strict_mono I k
    · have := ih h'
      have := greedySeq_strict_mono I m
      omega

lemma greedySeq_inj (I : ℕ → Prop) {k m : ℕ} (h : k < m) : greedySeq I k < greedySeq I m := by
  have := greedySeq_mono_add I k m h
  omega

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
lemma getVert_inj_of_shortest_walk {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h_neq : i ≠ j) : p.getVert i ≠ p.getVert j := by
  rcases lt_trichotomy i j with h_lt | h_eq | h_gt
  · intro h_eq_vert
    let h_walk : G.Walk u v := (p.take i).append (p.drop j |>.copy h_eq_vert.symm rfl)
    have h_len : h_walk.length = i + (p.length - j) := by
      dsimp [h_walk]
      simp
      omega
    have h_dist_le : G.dist u v ≤ h_walk.length := G.dist_le h_walk
    rw [h_len, ← hp] at h_dist_le
    omega
  · contradiction
  · intro h_eq_vert
    let h_walk : G.Walk u v := (p.take j).append (p.drop i |>.copy h_eq_vert rfl)
    have h_len : h_walk.length = j + (p.length - i) := by
      dsimp [h_walk]
      simp
      omega
    have h_dist_le : G.dist u v ≤ h_walk.length := G.dist_le h_walk
    rw [h_len, ← hp] at h_dist_le
    omega

lemma ceil_div_3_le (L : ℕ) (m : ℕ) (hm : m = (⌈(L : ℝ) / 3⌉).toNat) (hm_pos : 0 < m) :
    3 * (m - 1) + 1 ≤ L := by
  have h0 : 0 ≤ (L : ℝ) / 3 := by positivity
  have h1 : (m : ℤ) = ⌈(L : ℝ) / 3⌉ := by
    rw [hm]
    exact Int.toNat_of_nonneg (Int.ceil_nonneg h0)
  have h2 : (m : ℝ) - 1 < (L : ℝ) / 3 := by
    have := Int.ceil_lt_add_one ((L : ℝ) / 3)
    have h1_real : (m : ℝ) = (⌈(L : ℝ) / 3⌉ : ℝ) := by exact_mod_cast h1
    linarith
  have h3 : (3 : ℝ) * ((m : ℝ) - 1) < (L : ℝ) := by linarith
  have h4 : (3 : ℤ) * ((m : ℤ) - 1) < (L : ℤ) := by exact_mod_cast h3
  omega

omit [Fintype α] [Nontrivial α] in
lemma path_indep_set (G : SimpleGraph α) {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (I : Set α) (hI : G.IsIndepSet I) :
    ∃ J : Finset α, (J : Set α) ⊆ {x ∈ p.support | x ∉ I} ∧
      G.IsIndepSet J ∧ (⌈(p.length : ℝ) / 3⌉).toNat ≤ J.card := by
  let I_prop : ℕ → Prop := fun n => n ≤ p.length ∧ p.getVert n ∈ I
  have hI_prop : ∀ n, I_prop n → ¬ I_prop (n + 1) := by
    intro n ⟨hn1, hn2⟩ ⟨hn3, hn4⟩
    have h_adj : G.Adj (p.getVert n) (p.getVert (n + 1)) := by
      apply p.adj_getVert_succ
      omega
    exact hI hn2 hn4 h_adj.ne h_adj
  let m := (⌈(p.length : ℝ) / 3⌉).toNat
  by_cases hm_pos : m = 0
  · use ∅
    refine ⟨by simp, by simp [SimpleGraph.IsIndepSet, Set.Pairwise], hm_pos.le⟩
  have hm_pos' : 0 < m := by omega
  have hm : 3 * (m - 1) + 1 ≤ p.length := ceil_div_3_le p.length m rfl hm_pos'
  let J_set := (Finset.range m).image (fun k => p.getVert (greedySeq I_prop k))
  use J_set
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [J_set, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨k, hk, rfl⟩
    have h_seq_le : greedySeq I_prop k ≤ p.length := by
      have := greedySeq_le I_prop k
      omega
    have h_not_I := greedySeq_not_I I_prop hI_prop k
    simp only [I_prop, not_and] at h_not_I
    have h_not_I' := h_not_I h_seq_le
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, h_not_I'⟩
    exact p.getVert_mem_support _
  · intro x hx y hy h_neq h_adj
    simp only [J_set, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨k, hk, rfl⟩
    rcases hy with ⟨l, hl, rfl⟩
    rcases lt_trichotomy k l with h_lt | h_eq | h_gt
    · have h_seq_k : greedySeq I_prop k ≤ p.length := by
        have := greedySeq_le I_prop k
        omega
      have h_seq_l : greedySeq I_prop l ≤ p.length := by
        have := greedySeq_le I_prop l
        omega
      have h_dist : greedySeq I_prop k + 2 ≤ greedySeq I_prop l := greedySeq_mono_add I_prop k l h_lt
      exact not_adj_of_shortest_walk p hp h_seq_k h_seq_l h_dist h_adj
    · subst h_eq
      contradiction
    · have h_seq_k : greedySeq I_prop k ≤ p.length := by
        have := greedySeq_le I_prop k
        omega
      have h_seq_l : greedySeq I_prop l ≤ p.length := by
        have := greedySeq_le I_prop l
        omega
      have h_dist : greedySeq I_prop l + 2 ≤ greedySeq I_prop k := greedySeq_mono_add I_prop l k h_gt
      exact not_adj_of_shortest_walk p hp h_seq_l h_seq_k h_dist h_adj.symm
  · have h_card : J_set.card = m := by
      dsimp [J_set]
      rw [Finset.card_image_of_injOn]
      · simp
      · intro k hk l hl h_eq
        simp only [Finset.mem_coe, Finset.mem_range] at hk hl
        rcases lt_trichotomy k l with h_lt | h_eq' | h_gt
        · have h_seq_k : greedySeq I_prop k ≤ p.length := by
            have := greedySeq_le I_prop k
            omega
          have h_seq_l : greedySeq I_prop l ≤ p.length := by
            have := greedySeq_le I_prop l
            omega
          have h_neq_vert := getVert_inj_of_shortest_walk p hp h_seq_k h_seq_l (greedySeq_inj I_prop h_lt).ne
          exact False.elim (h_neq_vert h_eq)
        · exact h_eq'
        · have h_seq_k : greedySeq I_prop k ≤ p.length := by
            have := greedySeq_le I_prop k
            omega
          have h_seq_l : greedySeq I_prop l ≤ p.length := by
            have := greedySeq_le I_prop l
            omega
          have h_neq_vert := getVert_inj_of_shortest_walk p hp h_seq_l h_seq_k (greedySeq_inj I_prop h_gt).ne
          exact False.elim (h_neq_vert h_eq.symm)
    omega

lemma isBipartite_of_indep_sets {V : Type*} (G : SimpleGraph V) (s t : Set V)
    (hs : G.IsIndepSet s) (ht : G.IsIndepSet t) : (G.induce (s ∪ t)).IsBipartite := by
  rw [isBipartite_iff_exists_isBipartiteWith]
  let s' : Set (↥(s ∪ t)) := {x | (x : V) ∈ s \ t}
  let t' : Set (↥(s ∪ t)) := {x | (x : V) ∈ t}
  use s', t'
  constructor
  · rw [Set.disjoint_iff]
    intro x hx
    simp only [Set.mem_inter_iff] at hx
    exact hx.1.2 hx.2
  · intro v w h_adj
    simp only [induce_adj] at h_adj
    have h_adj_G := h_adj
    rcases v.2 with hv_s | hv_t
    · rcases w.2 with hw_s | hw_t
      · exfalso; exact hs hv_s hw_s (by intro h; rw [h] at h_adj_G; exact G.irrefl h_adj_G) h_adj_G
      · by_cases hv_t : (v : V) ∈ t
        · exfalso; exact ht hv_t hw_t (by intro h; rw [h] at h_adj_G; exact G.irrefl h_adj_G) h_adj_G
        · left; exact ⟨⟨hv_s, hv_t⟩, hw_t⟩
    · rcases w.2 with hw_s | hw_t
      · by_cases hw_t : (w : V) ∈ t
        · exfalso; exact ht hv_t hw_t (by intro h; rw [h] at h_adj_G; exact G.irrefl h_adj_G) h_adj_G
        · right; exact ⟨hv_t, ⟨hw_s, hw_t⟩⟩
      · exfalso; exact ht hv_t hw_t (by intro h; rw [h] at h_adj_G; exact G.irrefl h_adj_G) h_adj_G

lemma isBipartite_of_indep_finsets {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t : Finset V)
    (hs : G.IsIndepSet s) (ht : G.IsIndepSet t) : (G.induce (s ∪ t : Finset V)).IsBipartite := by
  have h_eq : (↑(s ∪ t) : Set V) = ↑s ∪ ↑t := Finset.coe_union s t
  have h_bip := isBipartite_of_indep_sets G s t hs ht
  exact h_eq ▸ h_bip

omit [DecidableEq α] [Nontrivial α] in
lemma le_b (G : SimpleGraph α) (s : Finset α) (hs : (G.induce s).IsBipartite) :
    (s.card : ℝ) ≤ b G := by
  unfold b largestInducedBipartiteSubgraphSize
  have h_mem : s.card ∈ { n | ∃ s' : Finset α, (G.induce s').IsBipartite ∧ s'.card = n } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, rfl⟩
  have h_bdd : BddAbove { n | ∃ s' : Finset α, (G.induce s').IsBipartite ∧ s'.card = n } := by
    use Fintype.card α
    intro n hn
    rcases hn with ⟨s', _, rfl⟩
    exact s'.card_le_univ
  have h_le := le_csSup h_bdd h_mem
  exact_mod_cast h_le

/--
WOWII [Conjecture 17](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, the size `b(G)` of a largest induced bipartite subgraph
satisfies `b(G) ≥ α(G) + ⌈diam(G) / 3⌉`, where `α(G)` is the independence number of `G`
and `diam(G)` is the diameter of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture17 (G : SimpleGraph α) (h : G.Connected) :
    (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ b G := by
  -- Get maximum independent set I
  obtain ⟨I, hI_indep⟩ := G.exists_isNIndepSet_indepNum
  have hI_card' : (I.card : ℝ) = G.indepNum := by rw [hI_indep.card_eq]

  -- Get diametral path
  have h_nonempty : Nonempty α := inferInstance
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  have h_dist_eq_diam : G.dist u v = G.diam := by
    unfold SimpleGraph.dist SimpleGraph.diam
    rw [huv]

  -- Get shortest walk
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v

  -- Apply path_indep_set
  obtain ⟨J, hJ_sub, hJ_indep, hJ_card⟩ := path_indep_set G p hp (I : Set α) hI_indep.isIndepSet

  -- The bipartite subgraph is I ∪ J
  have h_bip := isBipartite_of_indep_finsets G I J hI_indep.isIndepSet hJ_indep
  have h_le := le_b G (I ∪ J) h_bip

  -- We just need to show that (I ∪ J).card ≥ G.indepNum + ⌈G.diam / 3⌉
  have h_disj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro x hx_I hx_J
    have hx_J_set : x ∈ (J : Set α) := hx_J
    have hx_sub := hJ_sub hx_J_set
    simp only [Set.mem_setOf_eq] at hx_sub
    exact hx_sub.2 hx_I

  have h_card_union : (I ∪ J).card = I.card + J.card := Finset.card_union_of_disjoint h_disj

  have h_J_card_le : (⌈(G.diam : ℝ) / 3⌉).toNat ≤ J.card := by
    have h_len : p.length = G.diam := by omega
    rw [← h_len]
    exact hJ_card

  have h_ceil_nonneg : 0 ≤ ⌈(G.diam : ℝ) / 3⌉ := by
    apply Int.ceil_nonneg
    positivity

  have h_J_card_real : (⌈(G.diam : ℝ) / 3⌉ : ℝ) ≤ (J.card : ℝ) := by
    have h_cast : ( (⌈(G.diam : ℝ) / 3⌉).toNat : ℤ ) ≤ (J.card : ℤ) := by exact_mod_cast h_J_card_le
    rw [Int.toNat_of_nonneg h_ceil_nonneg] at h_cast
    exact_mod_cast h_cast

  have h_final : (G.indepNum : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ ((I ∪ J).card : ℝ) := by
    rw [h_card_union, Nat.cast_add, hI_card']
    linarith

  linarith

end WrittenOnTheWallII.GraphConjecture17
