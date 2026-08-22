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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree

@[expose] public section

/-!
# Induced trees, neighbourhood independence, and girth

Supporting API for WOWII (Graffiti.pc) Conjecture 141.  Main results:

* `SimpleGraph.indepNeighborsCard_add_one_le_largestInducedTreeSize`: an
  independent set in a neighbourhood plus its centre induces a star, so
  `indepNeighborsCard G v + 1 ≤ largestInducedTreeSize G`.
* `SimpleGraph.isIndepSet_neighborSet_of_four_le_girth`: girth at least four
  makes every neighbourhood independent.
* `SimpleGraph.maxDegree_add_girth_le_largestInducedTreeSize_add_three`: for a
  connected cyclic graph of girth at least four,
  `Δ(G) + girth(G) ≤ largestInducedTreeSize G + 3` — a maximum-order induced
  tree containing the closed neighbourhood of a maximum-degree vertex admits an
  outside vertex with two neighbours on the tree; the tree path joining them
  closes a cycle (so has length at least `girth - 2`) and shares at most three
  vertices with the closed neighbourhood.
-/
namespace SimpleGraph

section PathHelpers

variable {β : Type*} {H : SimpleGraph β}

/-- In a path, at most one edge is incident to the first vertex. -/
private lemma path_start_unique_edge {a b u₁ u₂ : β} {p : H.Walk a b}
    (hp : p.IsPath) (h₁ : s(a, u₁) ∈ p.edges) (h₂ : s(a, u₂) ∈ p.edges) :
    u₁ = u₂ := by
  cases p with
  | nil => simp at h₁
  | @cons _ c _ h q =>
      rw [Walk.cons_isPath_iff] at hp
      have key : ∀ u : β, s(a, u) ∈ (Walk.cons h q).edges → u = c := by
        intro u hu
        rw [Walk.edges_cons, List.mem_cons] at hu
        rcases hu with heq | hmem
        · rcases Sym2.eq_iff.mp heq with ⟨-, huc⟩ | ⟨hac, -⟩
          · exact huc
          · exact absurd hac h.ne
        · exact absurd (Walk.fst_mem_support_of_mem_edges q hmem) hp.2
      rw [key u₁ h₁, key u₂ h₂]

/-- In a path, at most two edges are incident to any fixed vertex `w`: among
any three vertices joined to `w` by edges of the path, two coincide. -/
private lemma path_incident_edges_le_two {a b w u₁ u₂ u₃ : β} {p : H.Walk a b}
    (hp : p.IsPath) (h₁ : s(w, u₁) ∈ p.edges) (h₂ : s(w, u₂) ∈ p.edges)
    (h₃ : s(w, u₃) ∈ p.edges) :
    u₁ = u₂ ∨ u₁ = u₃ ∨ u₂ = u₃ := by
  induction p with
  | nil => simp at h₁
  | @cons x c y h q ih =>
      by_cases hwx : w = x
      · subst hwx
        exact Or.inl (path_start_unique_edge hp h₁ h₂)
      · rw [Walk.cons_isPath_iff] at hp
        have key : ∀ u : β, s(w, u) ∈ (Walk.cons h q).edges →
            (u = x ∧ w = c) ∨ s(w, u) ∈ q.edges := by
          intro u hu
          rw [Walk.edges_cons, List.mem_cons] at hu
          rcases hu with heq | hmem
          · rcases Sym2.eq_iff.mp heq with ⟨hwx', -⟩ | ⟨hwc, hux⟩
            · exact absurd hwx' hwx
            · exact Or.inl ⟨hux, hwc⟩
          · exact Or.inr hmem
        rcases key u₁ h₁ with ⟨hu₁, hwc⟩ | m₁
        · rcases key u₂ h₂ with ⟨hu₂, -⟩ | m₂
          · exact Or.inl (hu₁.trans hu₂.symm)
          · rcases key u₃ h₃ with ⟨hu₃, -⟩ | m₃
            · exact Or.inr (Or.inl (hu₁.trans hu₃.symm))
            · subst hwc
              exact Or.inr (Or.inr (path_start_unique_edge hp.1 m₂ m₃))
        · rcases key u₂ h₂ with ⟨hu₂, hwc⟩ | m₂
          · rcases key u₃ h₃ with ⟨hu₃, -⟩ | m₃
            · exact Or.inr (Or.inr (hu₂.trans hu₃.symm))
            · subst hwc
              exact Or.inr (Or.inl (path_start_unique_edge hp.1 m₁ m₃))
          · rcases key u₃ h₃ with ⟨-, hwc⟩ | m₃
            · subst hwc
              exact Or.inl (path_start_unique_edge hp.1 m₁ m₂)
            · exact ih hp.1 m₁ m₂ m₃

/-- A path visiting `a` and `b` contains a subpath between `a` and `b` (in one
of the two directions) whose support and edges lie in the original path. -/
private lemma exists_subpath_between {x y a b : β} {p : H.Walk x y} (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support) :
    (∃ q : H.Walk a b, q.IsPath ∧ q.support ⊆ p.support ∧ q.edges ⊆ p.edges) ∨
    (∃ q : H.Walk b a, q.IsPath ∧ q.support ⊆ p.support ∧ q.edges ⊆ p.edges) := by
  classical
  by_cases hbt : b ∈ (p.takeUntil a ha).support
  · exact Or.inr ⟨(p.takeUntil a ha).dropUntil b hbt, (hp.takeUntil ha).dropUntil hbt,
      List.Subset.trans ((p.takeUntil a ha).support_dropUntil_subset hbt)
        (p.support_takeUntil_subset ha),
      List.Subset.trans ((p.takeUntil a ha).edges_dropUntil_subset hbt)
        (p.edges_takeUntil_subset ha)⟩
  · have hbd : b ∈ (p.dropUntil a ha).support := by
      have h2 : b ∈ ((p.takeUntil a ha).append (p.dropUntil a ha)).support := by
        rw [p.take_spec ha]
        exact hb
      rcases (Walk.mem_support_append_iff _ _).mp h2 with hcase | hcase
      · exact absurd hcase hbt
      · exact hcase
    exact Or.inl ⟨(p.dropUntil a ha).takeUntil b hbd, (hp.dropUntil ha).takeUntil hbd,
      List.Subset.trans ((p.dropUntil a ha).support_takeUntil_subset hbd)
        (p.support_dropUntil_subset ha),
      List.Subset.trans ((p.dropUntil a ha).edges_takeUntil_subset hbd)
        (p.edges_dropUntil_subset ha)⟩

/-- In a tree, the unique path between two adjacent vertices is the single edge. -/
private lemma tree_isPath_eq_cons_nil (hH : H.IsTree) {a b : β} (hab : H.Adj a b)
    {q : H.Walk a b} (hq : q.IsPath) :
    q = Walk.cons hab Walk.nil := by
  obtain ⟨P, -, huniq⟩ := hH.existsUnique_path a b
  exact (huniq q hq).trans
    (huniq (Walk.cons hab Walk.nil) (Walk.IsPath.nil.cons (by simp [hab.ne]))).symm

/-- Two path-vertices adjacent (in a tree) to a common vertex `v` force `v`
onto the path: the unique tree path between them is the two-edge path through
`v`, and the subpath of `p` between them must be that path. -/
private lemma tree_center_mem_support (hH : H.IsTree)
    {v a b x y : β} (hva : H.Adj v a) (hvb : H.Adj v b) (hab : a ≠ b)
    {p : H.Walk x y} (hp : p.IsPath) (hap : a ∈ p.support) (hbp : b ∈ p.support) :
    v ∈ p.support := by
  rcases exists_subpath_between hp hap hbp with ⟨q, hq, hqs, -⟩ | ⟨q, hq, hqs, -⟩
  · have hr : (Walk.cons hva.symm (Walk.cons hvb Walk.nil)).IsPath :=
      (Walk.IsPath.nil.cons (by simp [hvb.ne])).cons (by simp [hva.ne', hab])
    obtain ⟨P, -, huniq⟩ := hH.existsUnique_path a b
    have heq : q = Walk.cons hva.symm (Walk.cons hvb Walk.nil) :=
      (huniq q hq).trans (huniq _ hr).symm
    apply hqs
    rw [heq]
    simp
  · have hr : (Walk.cons hvb.symm (Walk.cons hva Walk.nil)).IsPath :=
      (Walk.IsPath.nil.cons (by simp [hva.ne])).cons (by simp [hvb.ne', hab.symm])
    obtain ⟨P, -, huniq⟩ := hH.existsUnique_path b a
    have heq : q = Walk.cons hvb.symm (Walk.cons hva Walk.nil) :=
      (huniq q hq).trans (huniq _ hr).symm
    apply hqs
    rw [heq]
    simp

/-- If `v` lies on a path in a tree and `a` is a path-vertex adjacent to `v`,
then the edge `s(v, a)` is an edge of the path: the subpath of `p` between `v`
and `a` is the unique tree path, which is the single edge. -/
private lemma tree_edge_mem_of_center_mem (hH : H.IsTree)
    {v a x y : β} (hva : H.Adj v a)
    {p : H.Walk x y} (hp : p.IsPath) (hvp : v ∈ p.support) (hap : a ∈ p.support) :
    s(v, a) ∈ p.edges := by
  rcases exists_subpath_between hp hvp hap with ⟨q, hq, -, hqe⟩ | ⟨q, hq, -, hqe⟩
  · have heq := tree_isPath_eq_cons_nil hH hva hq
    apply hqe
    rw [heq]
    simp
  · have heq := tree_isPath_eq_cons_nil hH hva.symm hq
    have hmem : s(a, v) ∈ p.edges := by
      apply hqe
      rw [heq]
      simp
    rwa [Sym2.eq_swap] at hmem

end PathHelpers

section TreePath

variable {α : Type*} {G : SimpleGraph α}

/-- Mapping a path of an induced tree into `G` and closing it up through an
outside vertex `z` adjacent to both endpoints produces a cycle of length
`p.length + 2`, so the girth is at most `p.length + 2`. -/
lemma IsTree.girth_le_length_add_two_of_two_adj
    {s : Finset α}
    (_hT : (G.induce (s : Set α)).IsTree)
    {z a b : α}
    (hz : z ∉ s) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b)
    (p : (G.induce (s : Set α)).Walk ⟨a, Finset.mem_coe.mpr ha⟩ ⟨b, Finset.mem_coe.mpr hb⟩)
    (hp : p.IsPath) :
    G.girth ≤ p.length + 2 := by
  let e : G.induce (s : Set α) ↪g G := SimpleGraph.Embedding.induce _
  let q : G.Walk a b := p.map e.toHom
  have hq : q.IsPath := by
    dsimp [q]
    exact (Walk.map_isPath_iff_of_injective e.injective).2 hp
  have hq_length : q.length = p.length := by simp [q]
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
  have hclen : c.length = q.length + 2 := by simp [c, r]
  have hg := G.girth_le_length hc
  omega

/-- **Triangle-free bridge**: in a graph of girth at least `4`, the
neighborhood of any vertex is an independent set.  An edge inside a
neighborhood would close a `3`-cycle with the two star edges. -/
lemma isIndepSet_neighborSet_of_four_le_girth (hg4 : 4 ≤ G.girth) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  intro x hx y hy _ hadj
  have hvx : G.Adj v x := hx
  have hvy : G.Adj v y := hy
  have hxv : x ≠ v := hvx.ne'
  have hr : (Walk.cons hadj (Walk.cons hvy.symm Walk.nil)).IsPath :=
    (Walk.IsPath.nil.cons (by simp [hvy.ne'])).cons (by simp [hadj.ne, hxv])
  have hclose : s(v, x) ∉ (Walk.cons hadj (Walk.cons hvy.symm Walk.nil)).edges := by
    intro he
    rw [Walk.edges_cons, Walk.edges_cons, Walk.edges_nil] at he
    rcases List.mem_cons.mp he with he1 | he2
    · rcases Sym2.eq_iff.mp he1 with ⟨hvx', -⟩ | ⟨hvy', -⟩
      · exact hvx.ne hvx'
      · exact hvy.ne hvy'
    · rcases List.mem_cons.mp he2 with he3 | he4
      · rcases Sym2.eq_iff.mp he3 with ⟨hvy', -⟩ | ⟨-, hxy'⟩
        · exact hvy.ne hvy'
        · exact hadj.ne hxy'
      · simp at he4
  have hc : ((Walk.cons hadj (Walk.cons hvy.symm Walk.nil)).cons hvx).IsCycle :=
    (Walk.cons_isCycle_iff _ hvx).2 ⟨hr, hclose⟩
  have hg : G.girth ≤ 3 := by
    have hlen := G.girth_le_length hc
    simpa using hlen
  omega

end TreePath

section Main

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-- **Overlap lemma**: on a path `p` in an induced tree on `s`, at most `3`
vertices lie in the closed neighborhood of a fixed vertex `v ∈ s`.  Here the
path support is read off in `α` via `Subtype.val`. -/
lemma IsTree.card_support_inter_closedNeighborFinset_le_three
    [DecidableRel G.Adj] {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree) {v : α} (hv : v ∈ s)
    {x y : ↥(s : Set α)} {p : (G.induce (s : Set α)).Walk x y} (hp : p.IsPath) :
    ((p.support.map Subtype.val).toFinset ∩ insert v (G.neighborFinset v)).card ≤ 3 := by
  classical
  have hvs : v ∈ (s : Set α) := Finset.mem_coe.mpr hv
  set W : Finset α := (p.support.map Subtype.val).toFinset with hW
  have hmemW : ∀ u : α, u ∈ W ↔ ∃ û : ↥(s : Set α), û ∈ p.support ∧ (û : α) = u := by
    intro u
    simp [hW]
  have hadj_of_mem : ∀ (û : ↥(s : Set α)) (u : α), (û : α) = u → u ∈ G.neighborFinset v →
      (G.induce (s : Set α)).Adj ⟨v, hvs⟩ û := by
    intro û u hûu hu
    rw [induce_adj]
    show G.Adj v (û : α)
    rw [hûu]
    exact (G.mem_neighborFinset v u).mp hu
  have hinter : (W ∩ G.neighborFinset v).card ≤ 2 := by
    by_cases hvW : v ∈ W
    · -- `v` lies on the path: each neighbor of `v` on the path yields an edge of
      -- `p` at `v`, and a path has at most two edges at a fixed vertex.
      have hv'p : (⟨v, hvs⟩ : ↥(s : Set α)) ∈ p.support := by
        obtain ⟨û, hûp, hûv⟩ := (hmemW v).mp hvW
        have hûeq : û = (⟨v, hvs⟩ : ↥(s : Set α)) := Subtype.ext hûv
        rwa [hûeq] at hûp
      by_contra hgt
      push_neg at hgt
      obtain ⟨u₁, u₂, u₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hgt
      obtain ⟨û₁, hû₁p, hû₁⟩ := (hmemW u₁).mp (Finset.mem_inter.mp h1).1
      obtain ⟨û₂, hû₂p, hû₂⟩ := (hmemW u₂).mp (Finset.mem_inter.mp h2).1
      obtain ⟨û₃, hû₃p, hû₃⟩ := (hmemW u₃).mp (Finset.mem_inter.mp h3).1
      have e₁ := tree_edge_mem_of_center_mem hT
        (hadj_of_mem û₁ u₁ hû₁ (Finset.mem_inter.mp h1).2) hp hv'p hû₁p
      have e₂ := tree_edge_mem_of_center_mem hT
        (hadj_of_mem û₂ u₂ hû₂ (Finset.mem_inter.mp h2).2) hp hv'p hû₂p
      have e₃ := tree_edge_mem_of_center_mem hT
        (hadj_of_mem û₃ u₃ hû₃ (Finset.mem_inter.mp h3).2) hp hv'p hû₃p
      rcases path_incident_edges_le_two hp e₁ e₂ e₃ with h | h | h
      · exact h12 (by rw [← hû₁, ← hû₂, h])
      · exact h13 (by rw [← hû₁, ← hû₃, h])
      · exact h23 (by rw [← hû₂, ← hû₃, h])
    · -- `v` off the path: two distinct neighbors of `v` on the path would force
      -- `v` onto the path via the unique two-edge tree path through `v`.
      have hone : (W ∩ G.neighborFinset v).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u₁ hu₁ u₂ hu₂
        by_contra hne
        obtain ⟨û₁, hû₁p, hû₁⟩ := (hmemW u₁).mp (Finset.mem_inter.mp hu₁).1
        obtain ⟨û₂, hû₂p, hû₂⟩ := (hmemW u₂).mp (Finset.mem_inter.mp hu₂).1
        have hne' : û₁ ≠ û₂ := fun h => hne (by rw [← hû₁, ← hû₂, h])
        have hv'p := tree_center_mem_support hT
          (hadj_of_mem û₁ u₁ hû₁ (Finset.mem_inter.mp hu₁).2)
          (hadj_of_mem û₂ u₂ hû₂ (Finset.mem_inter.mp hu₂).2)
          hne' hp hû₁p hû₂p
        exact hvW ((hmemW v).mpr ⟨⟨v, hvs⟩, hv'p, rfl⟩)
      omega
  have hsub : W ∩ insert v (G.neighborFinset v) ⊆ insert v (W ∩ G.neighborFinset v) := by
    intro u hu
    rw [Finset.mem_inter, Finset.mem_insert] at hu
    rcases hu.2 with rfl | huN
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hu.1, huN⟩)
  calc (W ∩ insert v (G.neighborFinset v)).card
      ≤ (insert v (W ∩ G.neighborFinset v)).card := Finset.card_le_card hsub
    _ ≤ (W ∩ G.neighborFinset v).card + 1 := Finset.card_insert_le _ _
    _ ≤ 3 := by omega

/-- Extract an explicit independent neighbour set witnessing `indepNeighborsCard`. -/
lemma exists_indepSet_finset_neighbors (G : SimpleGraph α) (v : α) :
    ∃ S : Finset α, (∀ s ∈ S, G.Adj v s) ∧ G.IsIndepSet (S : Set α) ∧
      S.card = indepNeighborsCard G v := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  refine ⟨s.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hs.1 hx' hy' (fun h => hxy (congrArg Subtype.val h))
  · rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hs.2

omit [Fintype α] in
/-- A vertex together with an independent set of its neighbours induces a star,
hence a tree. -/
lemma isTree_induce_insert_indepSet_neighbors (v : α) (S : Finset α) :
    (∀ s ∈ S, G.Adj v s) → G.IsIndepSet (S : Set α) →
    (G.induce ((insert v S : Finset α) : Set α)).IsTree := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _ _
      have hset : ((insert v (∅ : Finset α) : Finset α) : Set α) = {v} := by simp
      rw [hset]
      letI : Nonempty ↥({v} : Set α) := ⟨⟨v, by simp⟩⟩
      letI : Subsingleton ↥({v} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        have ha : (a : α) = v := by simpa only [Set.mem_singleton_iff] using a.property
        have hb : (b : α) = v := by simpa only [Set.mem_singleton_iff] using b.property
        exact ha.trans hb.symm⟩
      exact IsTree.of_subsingleton
  | @insert s S₀ hs ih =>
      intro hadj hind
      have hadj₀ : ∀ x ∈ S₀, G.Adj v x := fun x hx =>
        hadj x (Finset.mem_insert_of_mem hx)
      have hind₀ : G.IsIndepSet (S₀ : Set α) :=
        hind.mono (Finset.coe_subset.mpr (Finset.subset_insert s S₀))
      have hT := ih hadj₀ hind₀
      have hsv : s ≠ v := (hadj s (Finset.mem_insert_self s S₀)).ne'
      have hzs : s ∉ insert v S₀ := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hsv, hs⟩
      have hza : G.Adj s v := (hadj s (Finset.mem_insert_self s S₀)).symm
      have huniq : ∀ ⦃b : α⦄, b ∈ insert v S₀ → G.Adj s b → b = v := by
        intro b hb hsb
        rcases Finset.mem_insert.mp hb with rfl | hbS₀
        · rfl
        · exfalso
          have hsS : s ∈ ((insert s S₀ : Finset α) : Set α) := by simp
          have hbS : b ∈ ((insert s S₀ : Finset α) : Set α) := by
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
            exact Or.inr hbS₀
          have hne : s ≠ b := fun h => hs (h ▸ hbS₀)
          exact hind hsS hbS hne hsb
      have hT' := hT.induce_insert_of_unique_adj hzs (Finset.mem_insert_self v S₀) hza huniq
      have hcomm : (insert v (insert s S₀) : Finset α) = insert s (insert v S₀) :=
        Finset.insert_comm v s S₀
      rw [hcomm]
      exact hT'

/-- The star bound: `indepNeighborsCard G v + 1 ≤ largestInducedTreeSize G`. -/
lemma indepNeighborsCard_add_one_le_largestInducedTreeSize (G : SimpleGraph α) (v : α) :
    indepNeighborsCard G v + 1 ≤ largestInducedTreeSize G := by
  classical
  obtain ⟨S, hadj, hind, hcard⟩ := exists_indepSet_finset_neighbors G v
  have hvS : v ∉ S := fun hv => G.irrefl (hadj v hv)
  have hT := isTree_induce_insert_indepSet_neighbors v S hadj hind
  have hbound := card_le_largestInducedTreeSize hT
  rwa [Finset.card_insert_of_notMem hvS, hcard] at hbound

omit [DecidableEq α] in
/-- The independence number of a neighbourhood is at most the degree. -/
lemma indepNeighborsCard_le_degree (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    indepNeighborsCard G v ≤ G.degree v := by
  classical
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  calc indepNeighborsCard G v = s.card := hs.2.symm
    _ ≤ Fintype.card (G.neighborSet v) := Finset.card_le_univ s
    _ = G.degree v := by
        rw [← G.card_neighborSet_eq_degree]

/-- **Main counting theorem**: in a connected graph with a cycle and girth at
least `4`, `Δ(G) + girth(G) ≤ largestInducedTreeSize G + 3`.

Proof: grow a maximum induced tree `s` through the closed neighborhood of a
maximum-degree vertex `v`; a boundary vertex `z` of `s` has two neighbors
`a ≠ b` in `s`, and the tree path from `a` to `b` closes through `z` into a
cycle, so it has at least `girth − 2` edges; the path meets the closed
neighborhood of `v` in at most `3` vertices, so inclusion–exclusion inside `s`
gives the bound. -/
theorem maxDegree_add_girth_le_largestInducedTreeSize_add_three
    (G : SimpleGraph α) [DecidableRel G.Adj] [Nontrivial α] (hG : G.Connected)
    (hcyc : ¬ G.IsAcyclic) (hg4 : 4 ≤ G.girth) :
    G.maxDegree + G.girth ≤ largestInducedTreeSize G + 3 := by
  classical
  obtain ⟨v, hvdeg⟩ := G.exists_maximal_degree_vertex
  have hadjS : ∀ u ∈ G.neighborFinset v, G.Adj v u := fun u hu =>
    (G.mem_neighborFinset v u).mp hu
  have hind : G.IsIndepSet ((G.neighborFinset v : Finset α) : Set α) := by
    rw [coe_neighborFinset]
    exact isIndepSet_neighborSet_of_four_le_girth hg4 v
  have hT0 := isTree_induce_insert_indepSet_neighbors v (G.neighborFinset v) hadjS hind
  obtain ⟨s, hrs, hT, hmax⟩ := exists_maximum_induced_tree_containing G
    (insert v (G.neighborFinset v))
    ⟨insert v (G.neighborFinset v), Finset.Subset.refl _, hT0⟩
  have hvs : v ∈ s := hrs (Finset.mem_insert_self v _)
  have hsne : s.Nonempty := ⟨v, hvs⟩
  have hsu : s ≠ Finset.univ := by
    intro hsu
    subst s
    have hset : (↑(Finset.univ : Finset α) : Set α) = Set.univ := by
      ext w
      simp
    rw [hset] at hT
    have hTuniv : (G.induce Set.univ).IsTree := hT
    have hGtree : G.IsTree := (induceUnivIso G).isTree_iff.mp hTuniv
    exact hcyc hGtree.IsAcyclic
  obtain ⟨z, hz, a, ha, b, hb, hab, hza, hzb⟩ :=
    exists_two_adj_of_maximum_induced_tree_containing hG hrs hsne hT hmax hsu
  obtain ⟨p, hp, -⟩ :=
    hT.existsUnique_path ⟨a, Finset.mem_coe.mpr ha⟩ ⟨b, Finset.mem_coe.mpr hb⟩
  have hgirth : G.girth ≤ p.length + 2 :=
    hT.girth_le_length_add_two_of_two_adj hz ha hb hab hza hzb p hp
  have hoverlap := hT.card_support_inter_closedNeighborFinset_le_three hvs hp
  have hWcard : (p.support.map Subtype.val).toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (hp.support_nodup.map Subtype.val_injective),
      List.length_map, Walk.length_support]
  have hr0card : (insert v (G.neighborFinset v)).card = G.maxDegree + 1 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
      card_neighborFinset_eq_degree, ← hvdeg]
  have hWsub : (p.support.map Subtype.val).toFinset ⊆ s := by
    intro u hu
    rw [List.mem_toFinset] at hu
    obtain ⟨û, hûp, rfl⟩ := List.mem_map.mp hu
    exact Finset.mem_coe.mp û.property
  have hie := Finset.card_union_add_card_inter
    (p.support.map Subtype.val).toFinset (insert v (G.neighborFinset v))
  have hle : ((p.support.map Subtype.val).toFinset ∪ insert v (G.neighborFinset v)).card ≤
      s.card := Finset.card_le_card (Finset.union_subset hWsub hrs)
  have hscard : s.card ≤ largestInducedTreeSize G := card_le_largestInducedTreeSize hT
  omega

end Main

end SimpleGraph
