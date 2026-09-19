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
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

/-!
# Largest induced tree

This file defines `largestInducedTreeSize`, the number of vertices in a largest
induced subtree of a graph.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`.
A tree is a connected acyclic graph; an induced tree is an induced subgraph that is a tree. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

omit [DecidableEq α] in
/-- The order of any induced tree is bounded by `largestInducedTreeSize`. -/
lemma card_le_largestInducedTreeSize {G : SimpleGraph α} {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    intro n hn
    obtain ⟨t, rfl, _⟩ := hn
    exact Finset.card_le_univ t
  · exact ⟨s, rfl, hs⟩

omit [DecidableEq α] in
/-- Every finite graph with a vertex has a nonempty induced tree. -/
lemma one_le_largestInducedTreeSize (G : SimpleGraph α) [Nonempty α] :
    1 ≤ largestInducedTreeSize G := by
  classical
  let x : α := Classical.choice (inferInstance : Nonempty α)
  let s : Finset α := {x}
  have hs : (s : Set α) = {x} := by
    simp [s]
  have hT : (G.induce (s : Set α)).IsTree := by
    rw [hs]
    letI : Nonempty ↥({x} : Set α) := ⟨⟨x, by simp⟩⟩
    letI : Subsingleton ↥({x} : Set α) := ⟨fun a b => by
      apply Subtype.ext
      have ha : (a : α) = x := Set.mem_singleton_iff.mp a.property
      have hb : (b : α) = x := Set.mem_singleton_iff.mp b.property
      exact ha.trans hb.symm⟩
    exact IsTree.of_subsingleton
  have hle := card_le_largestInducedTreeSize hT
  simpa [s] using hle
omit [Fintype α] in
/-- Attaching a new vertex along its unique neighbor in an induced tree gives a larger
induced tree. -/
lemma IsTree.induce_insert_of_unique_adj {G : SimpleGraph α} {s : Finset α} {z a : α}
    (hT : (G.induce (s : Set α)).IsTree)
    (_hz : z ∉ s) (ha : a ∈ s) (hza : G.Adj z a)
    (huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a) :
    (G.induce ((insert z s : Finset α) : Set α)).IsTree := by
  classical
  constructor
  · have hsconn : (G.induce (s : Set α)).Preconnected := hT.isConnected.preconnected
    have hzconn : (G.induce ({z} : Set α)).Preconnected := .of_subsingleton
    have hconn := connected_induce_union (v := z) (w := a) (s := ({z} : Set α))
      (t := (s : Set α)) hzconn hsconn (by simp) (by simpa using ha) hza
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using hconn
  · intro v c hc
    let e : G.induce ((insert z s : Finset α) : Set α) ↪g G :=
      SimpleGraph.Embedding.induce _
    let q : G.Walk (e v) (e v) := c.map e.toHom
    have hq : q.IsCycle := by
      dsimp [q]
      exact (Walk.map_isCycle_iff_of_injective e.injective).2 hc
    have hq_mem (w : α) (hw : w ∈ q.support) : w ∈ insert z s := by
      dsimp [q] at hw
      rw [Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      change (w' : α) ∈ insert z s
      exact w'.property
    by_cases hzq : z ∈ q.support
    · let r : G.Walk z z := q.rotate hzq
      have hr : r.IsCycle := by
        dsimp [r]
        exact hq.rotate hzq
      have hrsnd : r.snd ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support 1
      have hrpenultimate : r.penultimate ∈ q.support := by
        apply (q.mem_support_rotate_iff hzq).mp
        simpa only [r] using r.getVert_mem_support (r.length - 1)
      have hadj_snd : G.Adj z r.snd := r.adj_snd hr.not_nil
      have hadj_penultimate : G.Adj z r.penultimate :=
        (r.adj_penultimate hr.not_nil).symm
      have hsnd : r.snd ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrsnd) with heq | hmem
        · exact (hadj_snd.ne heq.symm).elim
        · exact hmem
      have hpenultimate : r.penultimate ∈ s := by
        rcases Finset.mem_insert.mp (hq_mem _ hrpenultimate) with heq | hmem
        · exact (hadj_penultimate.ne heq.symm).elim
        · exact hmem
      exact hr.snd_ne_penultimate <|
        (huniq hsnd hadj_snd).trans (huniq hpenultimate hadj_penultimate).symm
    · have hqs : ∀ w ∈ q.support, w ∈ (s : Set α) := by
        intro w hw
        rcases Finset.mem_insert.mp (hq_mem w hw) with heq | hmem
        · subst w
          exact (hzq hw).elim
        · simpa using hmem
      let qi := q.induce (s : Set α) hqs
      have hqi : qi.IsCycle := by
        apply (Walk.map_isCycle_iff_of_injective
          (f := (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom)
          (SimpleGraph.Embedding.induce (G := G) (s : Set α)).injective).mp
        rw [show qi.map (SimpleGraph.Embedding.induce (G := G) (s : Set α)).toHom = q by
          dsimp [qi]
          exact Walk.map_induce q hqs]
        exact hq
      exact hT.IsAcyclic qi hqi


omit [Fintype α] in
/-- A shortest walk induces a tree on its support. -/
lemma Walk.induce_support_isTree_of_length_eq_dist {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      have hsingle : (G.induce ({u} : Set α)).IsTree := by
        letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
        letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
          apply Subtype.ext
          have ha : (a : α) = u := by
            simpa only [Set.mem_singleton_iff] using a.property
          have hb : (b : α) = u := by
            simpa only [Set.mem_singleton_iff] using b.property
          exact ha.trans hb.symm⟩
        exact IsTree.of_subsingleton
      rw [hset]
      exact hsingle
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have hT := ih hptail
      have hpath : (p.cons huv).IsPath :=
        (p.cons huv).isPath_of_length_eq_dist hp
      have hu_not : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hpath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hbmem
        have hget : p.getVert i = b := by
          rw [← p.support_getElem_eq_getVert hi, hib]
        have hi_le : i ≤ p.length := by
          have hlen := p.length_support
          omega
        have hub' : G.Adj u (p.getVert i) := by simpa [hget] using hub
        let r : G.Walk u w := (p.drop i).cons hub'
        have hdistle : G.dist u w ≤ r.length := G.dist_le r
        have hlen : (p.cons huv).length ≤ r.length := by simpa [hp] using hdistle
        have hi0 : i = 0 := by
          simp only [Walk.length_cons, r, Walk.drop_length] at hlen
          omega
        subst i
        simpa using hget.symm
      have hsupp : (Walk.cons huv p).support.toFinset = insert u p.support.toFinset := by
        simp
      rw [hsupp]
      exact hT.induce_insert_of_unique_adj hu_not (by simp) huv huniq

/-- Removing one vertex from a shortest cycle gives an induced tree. -/
theorem girth_sub_one_le_largestInducedTreeSize (G : SimpleGraph α)
    (hcyc : ¬ G.IsAcyclic) :
    G.girth - 1 ≤ largestInducedTreeSize G := by
  classical
  obtain ⟨v, c, hc, hc_length⟩ := G.exists_girth_eq_length.mpr hcyc
  let p := c.tail.dropLast
  let s : Finset α := p.support.toFinset
  have hthree : 3 ≤ G.girth := hc.three_le_length.trans_eq hc_length.symm
  have hc_tail_path : c.tail.IsPath := by
    rw [Walk.isPath_def, c.support_tail_of_not_nil hc.not_nil]
    exact hc.support_nodup
  have hp_path : p.IsPath := by
    exact Walk.isPath_of_isSubwalk
      (Walk.isSubwalk_take c.tail (c.tail.length - 1)) hc_tail_path
  have hp_length : p.length = G.girth - 2 := by
    dsimp [p, Walk.dropLast]
    rw [Walk.take_length, Nat.min_eq_left (Nat.sub_le _ _)]
    have hlen := c.length_tail_add_one hc.not_nil
    rw [← hc_length] at hlen
    omega
  have hs_card : s.card = G.girth - 1 := by
    dsimp [s]
    rw [List.toFinset_card_of_nodup hp_path.support_nodup, Walk.length_support, hp_length]
    omega
  have hp_tree : (G.induce (s : Set α)).IsTree := by
    constructor
    · have hs_set : (s : Set α) = {y : α | y ∈ p.support} := by
        ext y
        simp [s]
      rw [hs_set]
      exact p.connected_induce_support
    · intro x d hd
      let e : G.induce (s : Set α) ↪g G := SimpleGraph.Embedding.induce _
      let q : G.Walk (e x) (e x) := d.map e.toHom
      have hq : q.IsCycle := by
        dsimp [q]
        exact (Walk.map_isCycle_iff_of_injective e.injective).2 hd
      have hd_tail_path : d.tail.IsPath := by
        rw [Walk.isPath_def, d.support_tail_of_not_nil hd.not_nil]
        exact hd.support_nodup
      have hd_length_le : d.length ≤ Fintype.card (s : Set α) := by
        have hlt := hd_tail_path.length_lt
        have hlen := d.length_tail_add_one hd.not_nil
        omega
      have hq_length : q.length = d.length := by
        simp [q]
      have hg_le : G.girth ≤ q.length := G.girth_le_length hq
      have hs_type_card : Fintype.card (s : Set α) = s.card := by
        simp
      rw [hq_length] at hg_le
      rw [hs_type_card, hs_card] at hd_length_le
      omega
  have hbound := card_le_largestInducedTreeSize hp_tree
  omega

omit [Fintype α] in
/-- Every pair of vertices in a connected graph lies in an induced tree. -/
lemma Connected.exists_induced_tree_containing_pair {G : SimpleGraph α}
    (hG : G.Connected) (x y : α) :
    ∃ s : Finset α, x ∈ s ∧ y ∈ s ∧ (G.induce (s : Set α)).IsTree := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist x y
  refine ⟨p.support.toFinset, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact Walk.induce_support_isTree_of_length_eq_dist p hp

omit [DecidableEq α] in
/-- A nonempty family of induced trees with prescribed vertices has a largest member. -/
lemma exists_maximum_induced_tree_containing (G : SimpleGraph α) (r : Finset α)
    (hr : ∃ s : Finset α, r ⊆ s ∧ (G.induce (s : Set α)).IsTree) :
    ∃ s : Finset α,
      r ⊆ s ∧
      (G.induce (s : Set α)).IsTree ∧
      ∀ t : Finset α, r ⊆ t →
        (G.induce (t : Set α)).IsTree → t.card ≤ s.card := by
  let A : Set (Finset α) :=
    {s | r ⊆ s ∧ (G.induce (s : Set α)).IsTree}
  have hAfin : A.Finite := Set.toFinite A
  have hAne : A.Nonempty := by
    obtain ⟨s, hrs, hT⟩ := hr
    exact ⟨s, hrs, hT⟩
  obtain ⟨s, hsA, hmax⟩ := Set.exists_max_image A Finset.card hAfin hAne
  dsimp [A] at hsA hmax
  refine ⟨s, hsA.1, hsA.2, ?_⟩
  intro t hrt hT
  exact hmax t ⟨hrt, hT⟩

/-- A nonempty proper vertex set in a connected graph has an edge across its boundary. -/
lemma Connected.exists_adj_finset_compl {G : SimpleGraph α}
    (hG : G.Connected) {s : Finset α} (hs : s.Nonempty) (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, G.Adj z a := by
  obtain ⟨u, hu⟩ := hs
  have hzex : ∃ z : α, z ∉ s := by
    by_contra hn
    push_neg at hn
    apply hsu
    exact Finset.eq_univ_of_forall hn
  obtain ⟨z, hz⟩ := hzex
  obtain ⟨p⟩ := hG u z
  obtain ⟨d, _, hd_in, hd_out⟩ :=
    p.exists_boundary_dart (s : Set α) (by simpa) (by simpa)
  exact ⟨d.snd, by simpa using hd_out, d.fst, by simpa using hd_in, d.adj.symm⟩

/-- A boundary vertex of a largest prescribed induced tree has two neighbors in the tree. -/
lemma exists_two_adj_of_maximum_induced_tree_containing
    {G : SimpleGraph α} {r s : Finset α}
    (hG : G.Connected) (hrs : r ⊆ s) (hs : s.Nonempty)
    (hT : (G.induce (s : Set α)).IsTree)
    (hmax : ∀ t : Finset α, r ⊆ t →
      (G.induce (t : Set α)).IsTree → t.card ≤ s.card)
    (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, ∃ b ∈ s,
      a ≠ b ∧ G.Adj z a ∧ G.Adj z b := by
  obtain ⟨z, hz, a, ha, hza⟩ := hG.exists_adj_finset_compl hs hsu
  by_cases hex : ∃ b ∈ s, b ≠ a ∧ G.Adj z b
  · obtain ⟨b, hb, hba, hzb⟩ := hex
    exact ⟨z, hz, a, ha, b, hb, hba.symm, hza, hzb⟩
  · have huniq : ∀ ⦃b : α⦄, b ∈ s → G.Adj z b → b = a := by
      intro b hb hzb
      by_contra hba
      exact hex ⟨b, hb, hba, hzb⟩
    have hT' := hT.induce_insert_of_unique_adj hz ha hza huniq
    have hrs' : r ⊆ insert z s := by
      intro v hv
      exact Finset.mem_insert_of_mem (hrs hv)
    have hle := hmax (insert z s) hrs' hT'
    have hcard := Finset.card_insert_of_notMem hz
    omega

/-- Two leaves outside the boundary cycle force an extra two vertices in the induced tree. -/
lemma IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
    {G : SimpleGraph α} [DecidableRel G.Adj] {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree)
    {x y z a b : α}
    (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1)
    (hz : z ∉ s) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b) :
    G.girth + 1 ≤ s.card := by
  let e : G.induce (s : Set α) ↪g G := SimpleGraph.Embedding.induce _
  obtain ⟨p, hp, _⟩ := hT.existsUnique_path ⟨a, by simpa⟩ ⟨b, by simpa⟩
  let q : G.Walk a b := p.map e.toHom
  have hq : q.IsPath := by
    dsimp [q]
    exact (Walk.map_isPath_iff_of_injective e.injective).2 hp
  have hq_s : ∀ w ∈ q.support, w ∈ s := by
    intro w hw
    dsimp [q] at hw
    rw [Walk.support_map] at hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact w'.property
  have hzq : z ∉ q.support := fun hzmem => hz (hq_s z hzmem)
  let r : G.Walk a z := q.concat hzb.symm
  have hr : r.IsPath := hq.concat hzq hzb.symm
  have hclose : s(z, a) ∉ r.edges := by
    intro he
    dsimp [r] at he
    simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact hzq (q.fst_mem_support_of_mem_edges he)
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
      rcases he with ⟨hzb', haz⟩ | ⟨_, hab'⟩
      · exact hza.ne haz.symm
      · exact hab hab'
  let c : G.Walk z z := r.cons hza
  have hc : c.IsCycle := by
    dsimp [c]
    exact (Walk.cons_isCycle_iff r hza).2 ⟨hr, hclose⟩
  have hsubx : (G.neighborSet x).Subsingleton := by
    obtain ⟨nx, hnx, huniqx⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    intro u hu v hv
    exact (huniqx u hu).trans (huniqx v hv).symm
  have hsuby : (G.neighborSet y).Subsingleton := by
    obtain ⟨ny, hny, huniqy⟩ := degree_eq_one_iff_existsUnique_adj.mp hy
    intro u hu v hv
    exact (huniqy u hu).trans (huniqy v hv).symm
  have hxz : x ≠ z := fun hxz => hz (hxz ▸ hxs)
  have hyz : y ≠ z := fun hyz => hz (hyz ▸ hys)
  have hxnot : x ∉ c.support :=
    hc.isTrail.not_mem_support_of_subsingleton_neighborSet hxz hxz hsubx
  have hynot : y ∉ c.support :=
    hc.isTrail.not_mem_support_of_subsingleton_neighborSet hyz hyz hsuby
  have hqC : ∀ ⦃w : α⦄, w ∈ q.support → w ∈ c.support := by
    intro w hw
    have hwr : w ∈ r.support := by
      dsimp [r]
      exact q.support_subset_support_concat hzb.symm hw
    dsimp [c]
    exact r.support_subset_support_cons hza hwr
  have hqsub : q.support.toFinset ⊆ (s.erase x).erase y := by
    intro w hw
    have hwq : w ∈ q.support := by simpa using hw
    have hws : w ∈ s := hq_s w hwq
    have hwx : w ≠ x := by
      intro hwx
      subst w
      exact hxnot (hqC hwq)
    have hwy : w ≠ y := by
      intro hwy
      subst w
      exact hynot (hqC hwq)
    simp [hws, hwx, hwy]
  have hqcard : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
  have hy_erase : y ∈ s.erase x := by simp [hys, hxy.symm]
  have hcard := Finset.card_le_card hqsub
  rw [hqcard, Finset.card_erase_of_mem hy_erase,
    Finset.card_erase_of_mem hxs] at hcard
  have hclen : c.length = q.length + 2 := by simp [c, r]
  have hg := G.girth_le_length hc
  omega

/-- Two distinct leaves in a connected cyclic graph yield an induced tree of order at least girth plus one. -/
lemma girth_add_one_le_largestInducedTreeSize_of_two_leaves
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hcyc : ¬ G.IsAcyclic)
    {x y : α} (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨t, hxt, hyt, hTt⟩ :=
    Connected.exists_induced_tree_containing_pair hG x y
  have hr : ∃ u : Finset α,
      ({x, y} : Finset α) ⊆ u ∧ (G.induce (u : Set α)).IsTree := by
    refine ⟨t, ?_, hTt⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hxt
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact hyt
  obtain ⟨s, hrs, hT, hmax⟩ :=
    exists_maximum_induced_tree_containing G {x, y} hr
  have hxs : x ∈ s := hrs (by simp)
  have hys : y ∈ s := hrs (by simp)
  have hs : s.Nonempty := ⟨x, hxs⟩
  have hsu : s ≠ Finset.univ := by
    intro hsu
    subst s
    have hset : (↑(Finset.univ : Finset α) : Set α) = Set.univ := by
      ext v
      simp
    rw [hset] at hT
    have hTuniv : (G.induce Set.univ).IsTree := hT
    have hGtree : G.IsTree := (induceUnivIso G).isTree_iff.mp hTuniv
    exact hcyc hGtree.IsAcyclic
  obtain ⟨z, hz, a, ha, b, hb, hab, hza, hzb⟩ :=
    exists_two_adj_of_maximum_induced_tree_containing
      hG hrs hs hT hmax hsu
  have hbound : G.girth + 1 ≤ s.card :=
    IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
      hT hxs hys hxy hx hy hz ha hb hab hza hzb
  exact hbound.trans (card_le_largestInducedTreeSize hT)
end SimpleGraph
