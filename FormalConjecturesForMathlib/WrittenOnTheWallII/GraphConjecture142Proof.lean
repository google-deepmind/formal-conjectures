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
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

/-!
# Formal proof of Written on the Wall II Conjecture 142

We prove the stronger integral estimate
`ecc(B) + girth - girth / 3 ≤ tree`, where `B` is the graph periphery.
The proof constructs induced trees from a shortest cycle and carefully selected
geodesic tails, with separate sharp arguments for girths three and four and for
the two nonzero residue classes modulo three.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

omit [Fintype α] in
/-- Attaching a new vertex along its unique neighbor in an induced tree gives a larger
induced tree. -/
lemma IsTree.induce_insert_of_unique_adj {s : Finset α} {z a : α}
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
/-- A chordless path with exactly one edge to an induced tree can be spliced onto it.
This is the graph-theoretic core of the interacting-descent case in W142 L7(b). -/
lemma Walk.IsPath.induce_union_isTree_of_unique_attachment
    {s : Finset α} {a b r : α} (q : G.Walk a b)
    (hq : q.IsPath)
    (hsTree : (G.induce (s : Set α)).IsTree)
    (hdisj : ∀ ⦃x : α⦄, x ∈ q.support → x ∉ s)
    (hchordless : ∀ ⦃x y : α⦄, x ∈ q.support → y ∈ q.support →
      G.Adj x y → s(x, y) ∈ q.edges)
    (hr : r ∈ s) (har : G.Adj a r)
    (hcross : ∀ ⦃x y : α⦄, x ∈ q.support → y ∈ s → G.Adj x y → x = a ∧ y = r) :
    (G.induce (((s ∪ q.support.toFinset : Finset α) : Finset α) : Set α)).IsTree := by
  induction q generalizing s r with
  | @nil u0 =>
      have htree := hsTree.induce_insert_of_unique_adj (hdisj (by simp)) hr har
        (fun _ hy hay => (hcross (by simp) hy hay).2)
      have hset : s ∪ (Walk.nil : G.Walk u0 u0).support.toFinset = insert u0 s := by
        ext x
        simp
      rwa [hset]
  | @cons u0 v0 w0 hu0v0 p ih =>
      have hqFull := hq
      rw [Walk.cons_isPath_iff] at hq
      have hu0_not_p : u0 ∉ p.support := hq.2
      have hu0_not_s : u0 ∉ s := hdisj (by simp)
      have hsU : (G.induce ((insert u0 s : Finset α) : Set α)).IsTree :=
        hsTree.induce_insert_of_unique_adj hu0_not_s hr har
          (fun _ hy hay => (hcross (by simp) hy hay).2)
      have hpdisj : ∀ ⦃x : α⦄, x ∈ p.support → x ∉ insert u0 s := by
        intro x hx hxin
        rcases Finset.mem_insert.mp hxin with rfl | hxs
        · exact hu0_not_p hx
        · exact hdisj (by simp [hx]) hxs
      have hpchordless : ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ p.support →
          G.Adj x y → s(x, y) ∈ p.edges := by
        intro x y hx hy hxy
        have he := hchordless (by simp [hx]) (by simp [hy]) hxy
        rw [Walk.edges_cons] at he
        rcases List.mem_cons.mp he with he | he
        · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (hu0_not_p hx).elim
          · exact (hu0_not_p hy).elim
        · exact he
      have hpcross : ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ insert u0 s →
          G.Adj x y → x = v0 ∧ y = u0 := by
        intro x y hx hy hxy
        rcases Finset.mem_insert.mp hy with hyu | hys
        · subst y
          have he : s(u0, x) ∈ (p.cons hu0v0).edges := by
            exact hchordless (by simp) (by simp [hx]) hxy.symm
          have hxv : x = v0 := by simpa using hqFull.eq_snd_of_mem_edges he
          exact ⟨hxv, rfl⟩
        · have hc := hcross (by simp [hx]) hys hxy
          exact (hu0_not_p (hc.1 ▸ hx)).elim
      have hrec := ih hq.1 hsU hpdisj hpchordless (by simp) hu0v0.symm
        (fun x y hx hy hxy => hpcross hx hy hxy)
      have hset : s ∪ (p.cons hu0v0).support.toFinset =
          insert u0 s ∪ p.support.toFinset := by
        ext x
        simp
      rwa [hset]
lemma IsTree.induce_union_of_disjoint_of_unique_adj_splice
    {A B : Finset α}
    (hA : (G.induce (A : Set α)).IsTree)
    (hB : (G.induce (B : Set α)).IsTree)
    (hdisj : Disjoint A B)
    (hcross : ∃! e : α × α, e.1 ∈ A ∧ e.2 ∈ B ∧ G.Adj e.1 e.2) :
    (G.induce ((A ∪ B : Finset α) : Set α)).IsTree := by
  classical
  obtain ⟨⟨a, b⟩, hab, huniq⟩ := hcross
  rcases hab with ⟨haA, hbB, hab⟩
  let EA : Finset (Sym2 α) := G.edgeFinset ∩ A.sym2
  let EB : Finset (Sym2 α) := G.edgeFinset ∩ B.sym2
  let EU : Finset (Sym2 α) := G.edgeFinset ∩ (A ∪ B).sym2
  have edgeCardInduce (S : Finset α) :
      Nat.card (G.induce (S : Set α)).edgeSet =
        (G.edgeFinset ∩ S.sym2).card := by
    letI : Fintype (S : Set α) :=
      Subtype.fintype (fun x => x ∈ (S : Set α))
    have hm := SimpleGraph.map_edgeFinset_induce (G := G) (s := (S : Set α))
    have hc := congrArg Finset.card hm
    rw [Finset.card_map] at hc
    calc
      Nat.card (G.induce (S : Set α)).edgeSet =
          (G.induce (S : Set α)).edgeFinset.card := by
            rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
      _ = _ := hc
      _ = (G.edgeFinset ∩ S.sym2).card := by
        congr 1
        apply Finset.ext
        intro e
        induction e using Sym2.inductionOn
        simp
  have hconn : (G.induce ((A ∪ B : Finset α) : Set α)).Connected := by
    have hu := connected_induce_union (v := a) (w := b)
      (s := (A : Set α)) (t := (B : Set α))
      hA.isConnected.preconnected hB.isConnected.preconnected
      (by simpa using haA) (by simpa using hbB) hab
    have hset : ((A ∪ B : Finset α) : Set α) =
        (A : Set α) ∪ (B : Set α) := by
      ext x
      simp
    rw [hset]
    exact hu
  have hpart : EU = (EA ∪ EB) ∪ {s(a, b)} := by
    apply Finset.ext
    rw [Sym2.forall]
    intro x y
    simp only [EU, EA, EB, Finset.mem_inter, mem_edgeFinset,
      Finset.mk_mem_sym2_iff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hxy, hx, hy⟩
      rcases hx with hxA | hxB
      · rcases hy with hyA | hyB
        · exact Or.inl (Or.inl ⟨hxy, hxA, hyA⟩)
        · right
          have heq := huniq (x, y) ⟨hxA, hyB, hxy⟩
          simpa using congrArg (fun e : α × α => s(e.1, e.2)) heq
      · rcases hy with hyA | hyB
        · right
          have heq := huniq (y, x) ⟨hyA, hxB, hxy.symm⟩
          have hsEq : s(y, x) = s(a, b) :=
            congrArg (fun e : α × α => s(e.1, e.2)) heq
          simpa only [Sym2.eq_swap] using hsEq
        · exact Or.inl (Or.inr ⟨hxy, hxB, hyB⟩)
    · rintro (hinternal | hedge)
      · rcases hinternal with hAedge | hBedge
        · rcases hAedge with ⟨hxy, hxA, hyA⟩
          exact ⟨hxy, Or.inl hxA, Or.inl hyA⟩
        · rcases hBedge with ⟨hxy, hxB, hyB⟩
          exact ⟨hxy, Or.inr hxB, Or.inr hyB⟩
      · rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hab, Or.inl haA, Or.inr hbB⟩
        · exact ⟨hab.symm, Or.inr hbB, Or.inl haA⟩
  have hEAEB : Disjoint EA EB := by
    rw [Finset.disjoint_left, Sym2.forall]
    intro x y
    simp only [EA, EB, Finset.mem_inter, Finset.mk_mem_sym2_iff]
    rintro ⟨_, hxA, _⟩ ⟨_, hxB, _⟩
    exact (Finset.disjoint_left.mp hdisj hxA hxB).elim
  have hEAEBedge : Disjoint (EA ∪ EB) {s(a, b)} := by
    rw [Finset.disjoint_left]
    intro e he heSingle
    have heEq : e = s(a, b) := Finset.mem_singleton.mp heSingle
    subst e
    rcases Finset.mem_union.mp he with heA | heB
    · have hbA : b ∈ A :=
        (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp heA).2).2
      exact (Finset.disjoint_left.mp hdisj hbA hbB).elim
    · have haB : a ∈ B :=
        (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp heB).2).1
      exact (Finset.disjoint_left.mp hdisj haA haB).elim
  have hEUcard : EU.card = EA.card + EB.card + 1 := by
    rw [hpart, Finset.card_union_of_disjoint hEAEBedge,
      Finset.card_union_of_disjoint hEAEB, Finset.card_singleton]
  have hAcount : EA.card + 1 = A.card := by
    have ht := (isTree_iff_connected_and_card.mp hA).2
    have htype : Nat.card (A : Set α) = A.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [edgeCardInduce A, htype] at ht
    exact ht
  have hBcount : EB.card + 1 = B.card := by
    have ht := (isTree_iff_connected_and_card.mp hB).2
    have htype : Nat.card (B : Set α) = B.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [edgeCardInduce B, htype] at ht
    exact ht
  rw [isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hUtype : Nat.card ((A ∪ B : Finset α) : Set α) =
      (A ∪ B).card := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hUcard : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hdisj
  have hInduceCard := edgeCardInduce (A ∪ B)
  rw [hInduceCard, show G.edgeFinset ∩ (A ∪ B).sym2 = EU by rfl,
    hEUcard, hUtype, hUcard]
  omega

omit [DecidableEq α] in
/-- Every concrete induced tree is bounded by `largestInducedTreeSize`. -/
lemma IsTree.card_le_largestInducedTreeSize_splice {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨t, rfl, -⟩
      exact t.card_le_univ⟩
  · exact ⟨s, rfl, hs⟩
omit [Fintype α] in
/-- The spliced vertex set has the expected exact order. -/
lemma Walk.IsPath.card_union_support_of_disjoint
    {s : Finset α} {a b : α} (q : G.Walk a b) (hq : q.IsPath)
    (hdisj : ∀ ⦃x : α⦄, x ∈ q.support → x ∉ s) :
    (s ∪ q.support.toFinset).card = s.card + q.length + 1 := by
  have hd : Disjoint s q.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxs hxq
    exact hdisj (by simpa using hxq) hxs
  rw [Finset.card_union_of_disjoint hd]
  rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
  omega


omit [Fintype α] in
/-- If the left part has one edge into the retained cycle base and the right part has none,
their union has exactly that one attachment edge.  Ordered pairs make edge multiplicity explicit. -/
lemma Finset.existsUnique_adj_pair_union_of_unique_left_of_none_right
    {A B K : Finset α} {p k : α}
    (hpA : p ∈ A) (hkK : k ∈ K) (hpk : G.Adj p k)
    (hleft : ∀ ⦃x y : α⦄, x ∈ A → y ∈ K → G.Adj x y → x = p ∧ y = k)
    (hright : ∀ ⦃x y : α⦄, x ∈ B → y ∈ K → ¬G.Adj x y) :
    ∃! e : α × α, e.1 ∈ A ∪ B ∧ e.2 ∈ K ∧ G.Adj e.1 e.2 := by
  refine ⟨(p, k), ⟨Finset.mem_union_left _ hpA, hkK, hpk⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨hxy, hyK, hadj⟩
  rcases Finset.mem_union.mp hxy with hxA | hxB
  · rcases hleft hxA hyK hadj with ⟨rfl, rfl⟩
    rfl
  · exact (hright hxB hyK hadj).elim

omit [Fintype α] in
/-- Exact numerical end of the interacting-descent splice.  Here `hu` and `hv` are
the two descent heights, while `nuu` and `nu` are the depths of the joined vertices. -/
lemma Walk.IsPath.card_union_support_ge_dist_add_one
    {A : Finset α} {a b x y : α} (q : G.Walk a b) (hq : q.IsPath)
    (hdisj : ∀ ⦃w : α⦄, w ∈ q.support → w ∉ A)
    {hu hv nuu nu : ℕ} (hAcard : A.card = hu) (hqLength : q.length = hv - nu)
    (hnuuPos : 1 ≤ nuu) (hnuuLe : nuu ≤ hu)
    (hdist : G.dist x y ≤ (hu - nuu) + 1 + (hv - nu)) :
    G.dist x y + 1 ≤ (A ∪ q.support.toFinset).card := by
  have hcard := Walk.IsPath.card_union_support_of_disjoint q hq hdisj
  rw [hcard, hAcard, hqLength]
  omega

omit [Fintype α] in
/-- The complete local certificate produced after the maximal interacting index is chosen:
the splice is an induced tree, it has exactly one edge into the retained cycle path, and its
order is at least the endpoint distance plus one. -/
lemma Walk.IsPath.interacting_descent_splice_certificate
    {A K : Finset α} {a b r p k x y : α} (q : G.Walk a b) (hq : q.IsPath)
    (hATree : (G.induce (A : Set α)).IsTree)
    (hdisj : ∀ ⦃w : α⦄, w ∈ q.support → w ∉ A)
    (hchordless : ∀ ⦃w₁ w₂ : α⦄, w₁ ∈ q.support → w₂ ∈ q.support →
      G.Adj w₁ w₂ → s(w₁, w₂) ∈ q.edges)
    (hrA : r ∈ A) (har : G.Adj a r)
    (hcross : ∀ ⦃w₁ w₂ : α⦄, w₁ ∈ q.support → w₂ ∈ A →
      G.Adj w₁ w₂ → w₁ = a ∧ w₂ = r)
    (hpA : p ∈ A) (hkK : k ∈ K) (hpk : G.Adj p k)
    (hleft : ∀ ⦃w₁ w₂ : α⦄, w₁ ∈ A → w₂ ∈ K →
      G.Adj w₁ w₂ → w₁ = p ∧ w₂ = k)
    (hright : ∀ ⦃w₁ w₂ : α⦄, w₁ ∈ q.support → w₂ ∈ K → ¬G.Adj w₁ w₂)
    {hu hv nuu nu : ℕ} (hAcard : A.card = hu) (hqLength : q.length = hv - nu)
    (hnuuPos : 1 ≤ nuu) (hnuuLe : nuu ≤ hu)
    (hdist : G.dist x y ≤ (hu - nuu) + 1 + (hv - nu)) :
    (G.induce ((A ∪ q.support.toFinset : Finset α) : Set α)).IsTree ∧
      (∃! e : α × α, e.1 ∈ A ∪ q.support.toFinset ∧ e.2 ∈ K ∧ G.Adj e.1 e.2) ∧
      G.dist x y + 1 ≤ (A ∪ q.support.toFinset).card := by
  refine ⟨Walk.IsPath.induce_union_isTree_of_unique_attachment q hq hATree hdisj
    hchordless hrA har hcross, ?_,
    Walk.IsPath.card_union_support_ge_dist_add_one q hq hdisj hAcard hqLength
      hnuuPos hnuuLe hdist⟩
  exact Finset.existsUnique_adj_pair_union_of_unique_left_of_none_right hpA hkK hpk hleft
    (fun w₁ w₂ hw₁ hw₂ hadj => hright (by simpa using hw₁) hw₂ hadj)

/-- A vertex interacts with a finite vertex set when it lies in the set or has a neighbor in it. -/
def InteractsFinset (G : SimpleGraph α) (A : Finset α) (x : α) : Prop :=
  x ∈ A ∨ ∃ y ∈ A, G.Adj x y

omit [Fintype α] [DecidableEq α] in
/-- The first interacting vertex of a descent walk.  With the walk directed from its top toward
the cycle, this is exactly the paper's interacting vertex of maximum depth. -/
lemma Walk.exists_first_interaction_index {u v : α} (q : G.Walk u v) (A : Finset α)
    (hex : ∃ i : ℕ, i < q.length ∧ InteractsFinset G A (q.getVert i)) :
    ∃ i : ℕ, i < q.length ∧ InteractsFinset G A (q.getVert i) ∧
      ∀ j : ℕ, j < i → ¬ InteractsFinset G A (q.getVert j) := by
  let i := Nat.find hex
  refine ⟨i, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hinter
  exact Nat.find_min hex hj ⟨lt_trans hj (Nat.find_spec hex).1, hinter⟩

omit [Fintype α] [DecidableEq α] in
/-- Before the first interacting index, vertices are both outside and nonadjacent to the other
descent. -/
lemma Walk.not_mem_and_forall_not_adj_before_first_interaction
    {u v : α} {q : G.Walk u v} {A : Finset α} {i : ℕ}
    (hfirst : ∀ j : ℕ, j < i → ¬ InteractsFinset G A (q.getVert j))
    {j : ℕ} (hj : j < i) :
    q.getVert j ∉ A ∧ ∀ y ∈ A, ¬G.Adj (q.getVert j) y := by
  have hn := hfirst j hj
  constructor
  · intro hmem
    exact hn (Or.inl hmem)
  · intro y hy hadj
    exact hn (Or.inr ⟨y, hy, hadj⟩)

omit [Fintype α] [DecidableEq α] in
/-- Every distance-realizing walk is chordless: any ambient edge between two support vertices is
one of the walk's own edges. -/
lemma Walk.chordless_of_length_eq_dist {u v x y : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) : s(x, y) ∈ p.edges := by
  induction p with
  | @nil u =>
      simp only [Walk.support_nil, List.mem_singleton] at hx hy
      subst x
      subst y
      exact (hxy.ne rfl).elim
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support → G.Adj u b → b = v := by
        intro b hb hub
        obtain ⟨i, hi, hib⟩ := List.mem_iff_getElem.mp hb
        have hget : p.getVert i = b := by
          rw [← p.support_getElem_eq_getVert hi, hib]
        have hiLe : i ≤ p.length := by
          have hlen := p.length_support
          omega
        have hub' : G.Adj u (p.getVert i) := by simpa [hget] using hub
        let r : G.Walk u w := (p.drop i).cons hub'
        have hdistLe : G.dist u w ≤ r.length := G.dist_le r
        have hlen : (p.cons huv).length ≤ r.length := by simpa [hp] using hdistLe
        have hi0 : i = 0 := by
          simp only [Walk.length_cons, r, Walk.drop_length] at hlen
          omega
        subst i
        simpa using hget.symm
      simp only [Walk.support_cons, List.mem_cons] at hx hy
      rw [Walk.edges_cons]
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy.ne rfl).elim
      · have hyv : y = v := huniq hy hxy
        simp [hyv]
      · have hxv : x = v := huniq hx hxy.symm
        simp [hxv, Sym2.eq_swap]
      · exact List.mem_cons_of_mem _ (ih hptail hx hy)

omit [Fintype α] [DecidableEq α] in
/-- A vertex of the reversed prefix has an index no larger than the prefix endpoint in the
original walk. -/
lemma Walk.exists_index_le_of_mem_support_reverse_take
    {u v w : α} (q : G.Walk u v) {i : ℕ} (hi : i ≤ q.length)
    (hw : w ∈ (q.take i).reverse.support) :
    ∃ j : ℕ, j ≤ i ∧ q.getVert j = w := by
  rw [Walk.support_reverse] at hw
  have hw' : w ∈ (q.take i).support := by simpa using hw
  obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hw'
  have hjLe : j ≤ i := by
    have hlen := (q.take i).length_support
    rw [Walk.take_length, Nat.min_eq_left hi] at hlen
    omega
  refine ⟨j, hjLe, ?_⟩
  have ht : (q.take i).getVert j = w := by
    rw [← (q.take i).support_getElem_eq_getVert hj, hjw]
  calc
    q.getVert j = (q.take i).getVert j := by
      rw [Walk.take_getVert, Nat.min_eq_right hjLe]
    _ = w := ht

omit [Fintype α] [DecidableEq α] in
/-- In the separated case where the top of the second descent is outside `A`, its first
interacting vertex is also outside `A`. -/
lemma Walk.getVert_first_interaction_not_mem
    {u v : α} (q : G.Walk u v) (A : Finset α) {i : ℕ}
    (hi : i < q.length)
    (hfirst : ∀ j : ℕ, j < i → ¬ InteractsFinset G A (q.getVert j))
    (hu : u ∉ A) : q.getVert i ∉ A := by
  cases i with
  | zero => simpa using hu
  | succ j =>
      intro hmem
      have hjLen : j < q.length := by omega
      have hadj := q.adj_getVert_succ hjLen
      exact hfirst j (Nat.lt_succ_self j) (Or.inr ⟨q.getVert (j + 1), hmem, hadj⟩)

omit [Fintype α] [DecidableEq α] in
/-- Maximality supplies all disjointness and cross-edge hypotheses for the reversed prefix,
once uniqueness of the selected vertex's neighbor in `A` has been established. -/
lemma Walk.reverse_take_disjoint_and_unique_cross_of_first
    {u v r : α} (q : G.Walk u v) (A : Finset α) {i : ℕ}
    (hi : i < q.length)
    (hfirst : ∀ j : ℕ, j < i → ¬ InteractsFinset G A (q.getVert j))
    (hu : u ∉ A)
    (huniq : ∀ ⦃y : α⦄, y ∈ A → G.Adj (q.getVert i) y → y = r) :
    (∀ ⦃w : α⦄, w ∈ (q.take i).reverse.support → w ∉ A) ∧
      ∀ ⦃w y : α⦄, w ∈ (q.take i).reverse.support → y ∈ A → G.Adj w y →
        w = q.getVert i ∧ y = r := by
  have hiLe : i ≤ q.length := Nat.le_of_lt hi
  have hiNot := q.getVert_first_interaction_not_mem A hi hfirst hu
  constructor
  · intro w hw hwA
    obtain ⟨j, hjLe, hjw⟩ := q.exists_index_le_of_mem_support_reverse_take hiLe hw
    by_cases hji : j < i
    · exact hfirst j hji (Or.inl (hjw ▸ hwA))
    · have hjiEq : j = i := by omega
      exact hiNot (hjiEq ▸ hjw ▸ hwA)
  · intro w y hw hy hwy
    obtain ⟨j, hjLe, hjw⟩ := q.exists_index_le_of_mem_support_reverse_take hiLe hw
    have hjiEq : j = i := by
      by_contra hne
      have hji : j < i := by omega
      exact hfirst j hji (Or.inr ⟨y, hy, hjw ▸ hwy⟩)
    have hwEq : w = q.getVert i := by exact (hjiEq ▸ hjw).symm
    refine ⟨hwEq, huniq hy ?_⟩
    simpa [hwEq] using hwy

omit [DecidableEq α] in
/-- A member of a finite target set bounds distance to that set. -/
lemma distToSet_le_dist_of_mem_public {S : Set α} (x : α) {s : α} (hs : s ∈ S) :
    G.distToSet x S ≤ G.dist x s := by
  unfold distToSet
  split_ifs with h
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Set.mem_toFinset.mpr hs))
  · exact Nat.zero_le _

omit [DecidableEq α] in
/-- Distance to a nonempty finite target set is attained by one of its vertices. -/
lemma exists_mem_dist_eq_distToSet {S : Set α} (x : α) (hS : S.Nonempty) :
    ∃ s ∈ S, G.distToSet x S = G.dist x s := by
  have hSf : S.toFinset.Nonempty := Set.toFinset_nonempty.mpr hS
  unfold distToSet
  rw [dif_pos hSf]
  have hm := Finset.min'_mem (S.toFinset.image fun s => G.dist x s)
    (Finset.Nonempty.image hSf _)
  rcases Finset.mem_image.mp hm with ⟨s, hs, heq⟩
  refine ⟨s, Set.mem_toFinset.mp hs, ?_⟩
  exact heq.symm

omit [DecidableEq α] in
/-- Along a walk that realizes distance to a target set, the distance-to-set of the vertex at
index `i` is exactly the number of remaining edges. -/
lemma Walk.distToSet_getVert_eq_length_sub_of_nearest
    {S : Set α} {u v : α} (hconn : G.Connected) (p : G.Walk u v)
    (hv : v ∈ S) (hp : p.length = G.distToSet u S) {i : ℕ} (hi : i ≤ p.length) :
    G.distToSet (p.getVert i) S = p.length - i := by
  have hupperSet := distToSet_le_dist_of_mem_public (G := G) (p.getVert i) hv
  have hupperDist : G.dist (p.getVert i) v ≤ (p.drop i).length := G.dist_le (p.drop i)
  have hupper : G.distToSet (p.getVert i) S ≤ p.length - i := by
    rw [Walk.drop_length] at hupperDist
    omega
  obtain ⟨s, hsS, hsEq⟩ := exists_mem_dist_eq_distToSet (G := G) (p.getVert i) ⟨v, hv⟩
  obtain ⟨r, hr⟩ := hconn.exists_walk_length_eq_dist (p.getVert i) s
  let w : G.Walk u s := (p.take i).append r
  have hbase := distToSet_le_dist_of_mem_public (G := G) u hsS
  have hdistWalk : G.dist u s ≤ w.length := G.dist_le w
  have htake : (p.take i).length = i := by
    rw [Walk.take_length, Nat.min_eq_left hi]
  have hwlen : w.length = i + G.distToSet (p.getVert i) S := by
    simp only [w, Walk.length_append, htake, hr, hsEq]
  have hlower : p.length ≤ w.length := by
    calc
      p.length = G.distToSet u S := hp
      _ ≤ G.dist u s := hbase
      _ ≤ w.length := hdistWalk
  rw [hwlen] at hlower
  omega

omit [DecidableEq α] in
/-- Adjacent vertices have distance-to-set values differing by at most one (one direction). -/
lemma distToSet_le_add_one_of_adj {S : Set α} {x y : α} (hS : S.Nonempty)
    (hxy : G.Adj x y) : G.distToSet x S ≤ G.distToSet y S + 1 := by
  obtain ⟨s, hsS, hsEq⟩ := exists_mem_dist_eq_distToSet (G := G) y hS
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) x hsS
  have hdiff := hxy.symm.diff_dist_adj (u := s)
  have hsx : G.dist s x = G.dist x s := G.dist_comm
  have hsy : G.dist s y = G.dist y s := G.dist_comm
  rw [hsx, hsy, ← hsEq] at hdiff
  omega

omit [DecidableEq α] in
/-- A vertex before the endpoint of a nearest-set walk is outside the target set. -/
lemma Walk.getVert_not_mem_of_length_eq_distToSet
    {S : Set α} {u v : α} (p : G.Walk u v) (hp : p.length = G.distToSet u S)
    {i : ℕ} (hi : i < p.length) : p.getVert i ∉ S := by
  intro hiS
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) u hiS
  have hdistLe : G.dist u (p.getVert i) ≤ (p.take i).length := G.dist_le (p.take i)
  have htake : (p.take i).length = i := by
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hbad : p.length ≤ i := by
    calc
      p.length = G.distToSet u S := hp
      _ ≤ G.dist u (p.getVert i) := hsetLe
      _ ≤ (p.take i).length := hdistLe
      _ = i := htake
  omega

omit [DecidableEq α] in
/-- If two vertices of one nearest descent are adjacent to the same vertex of a second descent,
their indices on the first descent differ by at most two. -/
lemma Walk.nearest_descents_neighbor_indices_within_two
    {S : Set α} {u ku v kv x₁ x₂ : α} (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ S) (hkv : kv ∈ S)
    (hp : p.length = G.distToSet u S) (hq : q.length = G.distToSet v S)
    {i : ℕ} (hi : i ≤ q.length)
    (hx₁ : x₁ ∈ p.support) (hx₂ : x₂ ∈ p.support)
    (ha₁ : G.Adj (q.getVert i) x₁) (ha₂ : G.Adj (q.getVert i) x₂) :
    ∃ j₁ j₂ : ℕ, j₁ ≤ p.length ∧ j₂ ≤ p.length ∧
      p.getVert j₁ = x₁ ∧ p.getVert j₂ = x₂ ∧ j₁ ≤ j₂ + 2 ∧ j₂ ≤ j₁ + 2 := by
  obtain ⟨j₁, hj₁, hj₁Le⟩ := Walk.mem_support_iff_exists_getVert.mp hx₁
  obtain ⟨j₂, hj₂, hj₂Le⟩ := Walk.mem_support_iff_exists_getVert.mp hx₂
  have hdq := q.distToSet_getVert_eq_length_sub_of_nearest hconn hkv hq hi
  have hdp₁ := p.distToSet_getVert_eq_length_sub_of_nearest hconn hku hp hj₁Le
  have hdp₂ := p.distToSet_getVert_eq_length_sub_of_nearest hconn hku hp hj₂Le
  have h12a := distToSet_le_add_one_of_adj (G := G) ⟨ku, hku⟩ ha₁
  have h12b := distToSet_le_add_one_of_adj (G := G) ⟨ku, hku⟩ ha₁.symm
  have h22a := distToSet_le_add_one_of_adj (G := G) ⟨ku, hku⟩ ha₂
  have h22b := distToSet_le_add_one_of_adj (G := G) ⟨ku, hku⟩ ha₂.symm
  rw [← hj₁, hdq, hdp₁] at h12a h12b
  rw [← hj₂, hdq, hdp₂] at h22a h22b
  refine ⟨j₁, j₂, hj₁Le, hj₂Le, hj₁, hj₂, ?_, ?_⟩ <;> omega

omit [Fintype α] [DecidableEq α] in
/-- Closing a path through a vertex outside its support gives a cycle. -/
private lemma Walk.IsPath.concat_two_isCycle_splice
    {a b x : α} {p : G.Walk a b} (hp : p.IsPath) (hab : a ≠ b)
    (hx : x ∉ p.support) (hbx : G.Adj b x) (hxa : G.Adj x a) :
    ((p.concat hbx).concat hxa).IsCycle := by
  have hpx : (p.concat hbx).IsPath := hp.concat hx hbx
  rw [← Walk.isCycle_reverse, Walk.reverse_concat, Walk.cons_isCycle_iff]
  refine ⟨(Walk.isPath_reverse_iff _).2 hpx, ?_⟩
  intro he
  have he' : s(x, a) ∈ (p.concat hbx).edges := by
    have he0 : s(a, x) ∈ (p.concat hbx).edges := by
      simpa only [Walk.edges_reverse, List.mem_reverse] using he
    rw [Sym2.eq_swap]
    exact he0
  have ha : a = (p.concat hbx).penultimate := hpx.eq_penultimate_of_mem_edges he'
  exact hab (by simpa using ha)

omit [Fintype α] [DecidableEq α] in
/-- Under girth at least five, a vertex outside a path of length at most two cannot be adjacent
to both distinct endpoints. -/
lemma Walk.IsPath.outside_neighbor_unique_of_length_le_two
    {a b x : α} {p : G.Walk a b} (hp : p.IsPath) (hlen : p.length ≤ 2)
    (hx : x ∉ p.support) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hg : 5 ≤ G.girth) : a = b := by
  by_contra hab
  have hc := hp.concat_two_isCycle_splice hab hx hxb.symm hxa
  have hbound := G.girth_le_length hc
  simp only [Walk.length_concat] at hbound
  omega

omit [DecidableEq α] in
/-- The selected first-interaction vertex has at most one neighbor on the other nearest descent.
The depth formula supplies the two-step index window and girth at least five excludes the resulting
triangle or quadrilateral. -/
lemma Walk.nearest_descents_selected_neighbor_unique
    {S : Set α} {u ku v kv x₁ x₂ : α} (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ S) (hkv : kv ∈ S)
    (hp : p.length = G.distToSet u S) (hq : q.length = G.distToSet v S)
    {i : ℕ} (hi : i < q.length) (hout : q.getVert i ∉ p.support)
    (hx₁ : x₁ ∈ p.support) (hx₂ : x₂ ∈ p.support)
    (ha₁ : G.Adj (q.getVert i) x₁) (ha₂ : G.Adj (q.getVert i) x₂)
    (hg : 5 ≤ G.girth) : x₁ = x₂ := by
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) u hku
  have hdistLe : G.dist u ku ≤ p.length := G.dist_le p
  have hpGeod : p.length = G.dist u ku := by omega
  have hpPath := p.isPath_of_length_eq_dist hpGeod
  obtain ⟨j₁, j₂, hj₁Le, hj₂Le, hj₁, hj₂, hj₁₂, hj₂₁⟩ :=
    p.nearest_descents_neighbor_indices_within_two hconn q hku hkv hp hq
      (Nat.le_of_lt hi) hx₁ hx₂ ha₁ ha₂
  have key : ∀ {a b : α} {ja jb : ℕ}, ja ≤ p.length → jb ≤ p.length →
      p.getVert ja = a → p.getVert jb = b → ja ≤ jb → jb ≤ ja + 2 →
      G.Adj (q.getVert i) a → G.Adj (q.getVert i) b → a = b := by
    intro a b ja jb hjaLe hjbLe hja hjb hjab hspan hqa hqb
    let r0 := (p.drop ja).take (jb - ja)
    have hsub : r0.IsSubwalk p :=
      (Walk.isSubwalk_take (p.drop ja) (jb - ja)).trans (Walk.isSubwalk_drop p ja)
    have hr0Path : r0.IsPath := isPath_of_isSubwalk hsub hpPath
    have hend : (p.drop ja).getVert (jb - ja) = b := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le hjab, hjb]
    let r : G.Walk a b := r0.copy hja hend
    have hrPath : r.IsPath := (Walk.isPath_copy r0 hja hend).2 hr0Path
    have hr0Len : r0.length = jb - ja := by
      dsimp [r0]
      rw [Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
    have hrLen : r.length ≤ 2 := by
      dsimp [r]
      rw [Walk.length_copy, hr0Len]
      omega
    have hrOut : q.getVert i ∉ r.support := by
      intro hmem
      apply hout
      apply hsub.support_subset
      dsimp [r] at hmem
      rw [Walk.support_copy] at hmem
      exact hmem
    exact hrPath.outside_neighbor_unique_of_length_le_two hrLen hrOut hqa hqb hg
  rcases le_total j₁ j₂ with hj | hj
  · exact key hj₁Le hj₂Le hj₁ hj₂ hj hj₂₁ ha₁ ha₂
  · exact (key hj₂Le hj₁Le hj₂ hj₁ hj hj₁₂ ha₂ ha₁).symm

omit [Fintype α] [DecidableEq α] in
/-- Every path with fewer vertices than the girth is chordless in the ambient graph. -/
lemma Walk.chordless_of_length_succ_lt_girth_splice
    {u v : α} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length + 1 < G.girth) :
    ∀ ⦃x y : α⦄, x ∈ p.support → y ∈ p.support →
      G.Adj x y → s(x, y) ∈ p.edges := by
  intro x y hx hy hxy
  by_contra hnot
  obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, hjEq, hjLe⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  have hijNe : i ≠ j := by
    intro hij
    apply hxy.ne
    calc
      x = p.getVert i := hiEq.symm
      _ = p.getVert j := by rw [hij]
      _ = y := hjEq
  have key : ∀ {i j : ℕ} {x y : α},
      p.getVert i = x → i ≤ p.length → p.getVert j = y → j ≤ p.length →
      i < j → G.Adj x y → s(x, y) ∉ p.edges → False := by
    intro i j x y hiEq hiLe hjEq hjLe hij hxy hnot
    let seg0 := (p.drop i).take (j - i)
    have hsub : seg0.IsSubwalk p := by
      exact (Walk.isSubwalk_take (p.drop i) (j - i)).trans
        (Walk.isSubwalk_drop p i)
    have hend : (p.drop i).getVert (j - i) = y := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le (Nat.le_of_lt hij), hjEq]
    let seg : G.Walk x y := seg0.copy hiEq hend
    have hsegPath : seg.IsPath := by
      dsimp [seg]
      simpa using isPath_of_isSubwalk hsub hp
    have hnotSeg : s(y, x) ∉ seg.edges := by
      intro he
      apply hnot
      have he0 : s(y, x) ∈ seg0.edges := by simpa [seg] using he
      have hep : s(y, x) ∈ p.edges := hsub.edges_subset he0
      simpa only [Sym2.eq_swap] using hep
    have hcyc : (Walk.cons hxy.symm seg).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      exact ⟨hsegPath, hnotSeg⟩
    have hgLe := G.girth_le_length hcyc
    have hsegLe : seg.length ≤ p.length := by
      simpa [seg] using Walk.length_le_of_isSubwalk hsub
    simp only [Walk.length_cons] at hgLe
    omega
  rcases lt_or_gt_of_ne hijNe with hij | hji
  · exact key hiEq hiLe hjEq hjLe hij hxy hnot
  · have hnotYX : s(y, x) ∉ p.edges := by
      simpa only [Sym2.eq_swap] using hnot
    exact key hjEq hjLe hiEq hiLe hji hxy.symm hnotYX

omit [Fintype α] in
/-- A path shorter than the girth by at least one vertex induces a tree. -/
lemma Walk.induce_support_isTree_of_isPath_of_length_succ_lt_girth_splice
    {u v : α} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length + 1 < G.girth) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hfull : (p.cons huv).IsPath := hp
      rw [Walk.cons_isPath_iff] at hp
      have htailShort : p.length + 1 < G.girth := by
        rw [Walk.length_cons] at hlen
        omega
      have htree := ih hp.1 htailShort
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hfull.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        have hedge := (p.cons huv).chordless_of_length_succ_lt_girth_splice
          hfull hlen (by simp) (by simp [hbmem]) hub
        simpa using hfull.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset =
          insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj huNot (by simp) huv huniq
omit [Fintype α] in
/-- Rotation preserves the length of a closed walk. -/
lemma Walk.length_rotate_splice {u v : α} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).length = c.length := by
  calc
    (c.rotate h).length = (c.rotate h).edges.length := (Walk.length_edges _).symm
    _ = c.edges.length := (c.rotate_edges h).perm.length_eq
    _ = c.length := Walk.length_edges c

omit [Fintype α] in
/-- Deleting a chosen vertex from a girth-realizing cycle leaves an induced path
on exactly `girth - 1` vertices. -/
lemma Walk.IsCycle.erase_vertex_path_certificate_splice
    {v root : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hroot : root ∈ c.support) (hcLength : c.length = G.girth) :
    let r := c.rotate hroot
    let base := r.tail.dropLast
    base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase root ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 := by
  let r := c.rotate hroot
  let base := r.tail.dropLast
  have hrCycle : r.IsCycle := by
    dsimp [r]
    exact hc.rotate hroot
  have hrLen : r.length = c.length := by
    dsimp [r]
    exact c.length_rotate_splice hroot
  have hrNotNil : ¬r.Nil := hrCycle.not_nil
  have hrThree : 3 ≤ r.length := hrCycle.three_le_length
  have htailLen : r.tail.length + 1 = r.length :=
    r.length_tail_add_one hrNotNil
  have htailPos : 0 < r.tail.length := by omega
  have hbaseSupp : base.support = r.tail.support.dropLast := by
    dsimp [base]
    rw [Walk.dropLast, Walk.take_support_eq_support_take_succ,
      List.dropLast_eq_take, r.tail.length_support]
    congr 1
    omega
  have htailSupp : r.tail.support = r.support.tail :=
    r.support_tail_of_not_nil hrNotNil
  have hbasePath : base.IsPath := by
    apply Walk.IsPath.mk'
    rw [hbaseSupp, htailSupp, List.dropLast_eq_take]
    exact hrCycle.support_nodup.take
  have hbaseLen : base.length = r.length - 2 := by
    dsimp [base]
    rw [Walk.dropLast, Walk.take_length]
    omega
  have hbaseShort : base.length + 1 < G.girth := by
    rw [hbaseLen, hrLen, hcLength]
    omega
  have hbaseTree :=
    base.induce_support_isTree_of_isPath_of_length_succ_lt_girth_splice
      hbasePath hbaseShort
  have hsupportEq :
      base.support.toFinset = c.support.toFinset.erase root := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_erase]
    constructor
    · intro hx
      have hxDrop : x ∈ r.tail.support.dropLast := by
        rw [← hbaseSupp]
        exact hx
      have hxTail : x ∈ r.tail.support := List.dropLast_subset _ hxDrop
      have hxRTail : x ∈ r.support.tail := by simpa [htailSupp] using hxTail
      have hxR : x ∈ r.support := List.mem_of_mem_tail hxRTail
      have hxCycle : x ∈ c.support :=
        (c.mem_support_rotate_iff hroot).mp hxR
      have htailNodup : r.tail.support.Nodup := by
        rw [htailSupp]
        exact hrCycle.support_nodup
      have hxNe : x ≠ root := by
        have hrel := htailNodup.rel_dropLast_getLast hxDrop
        simpa using hrel
      exact ⟨hxNe, hxCycle⟩
    · rintro ⟨hxNe, hxCycle⟩
      have hxR : x ∈ r.support :=
        (c.mem_support_rotate_iff hroot).mpr hxCycle
      have hxRTail : x ∈ r.support.tail := by
        rw [r.support_eq_cons] at hxR
        rcases List.mem_cons.mp hxR with hxRoot | hxTail
        · exact (hxNe hxRoot).elim
        · exact hxTail
      have hxTail : x ∈ r.tail.support := by
        rw [htailSupp]
        exact hxRTail
      have hxLast : x ≠ r.tail.support.getLast r.tail.support_ne_nil := by
        simpa using hxNe
      have hxDrop : x ∈ r.tail.support.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hxTail hxLast
      rw [hbaseSupp]
      exact hxDrop
  have hbaseCard : base.support.toFinset.card = c.length - 1 := by
    rw [List.toFinset_card_of_nodup hbasePath.support_nodup,
      base.length_support, hbaseLen, hrLen]
    omega
  exact ⟨hbasePath, hsupportEq, hbaseTree, hbaseCard⟩
omit [Fintype α] in
/-- A distance-realizing walk induces a tree on its support. -/
lemma Walk.induce_support_isTree_of_length_eq_dist {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset : (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have htree := ih hptail
      have hpath : (p.cons huv).IsPath := (p.cons huv).isPath_of_length_eq_dist hp
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hpath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbmem : b ∈ p.support := by simpa using hb
        have hedge := (p.cons huv).chordless_of_length_eq_dist hp
          (by simp) (by simp [hbmem]) hub
        simpa using hpath.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset = insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj huNot (by simp) huv huniq

/-- The outside vertices of a nontrivial nearest-set descent form an induced tree of order equal
to the descent length. -/
lemma Walk.nearest_descent_dropLast_tree_and_card
    {S : Set α} {u v : α} (p : G.Walk u v) (hv : v ∈ S)
    (hp : p.length = G.distToSet u S) (hpos : 0 < p.length) :
    (G.induce (p.dropLast.support.toFinset : Set α)).IsTree ∧
      p.dropLast.support.toFinset.card = p.length := by
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) u hv
  have hdistLe : G.dist u v ≤ p.length := G.dist_le p
  have hpGeod : p.length = G.dist u v := by omega
  have hdropGeod : p.dropLast.length = G.dist u p.penultimate :=
    length_eq_dist_of_subwalk hpGeod (Walk.isSubwalk_take p (p.length - 1))
  have htree := p.dropLast.induce_support_isTree_of_length_eq_dist hdropGeod
  have hpPath := p.isPath_of_length_eq_dist hpGeod
  have hdropPath : p.dropLast.IsPath :=
    isPath_of_isSubwalk (Walk.isSubwalk_take p (p.length - 1)) hpPath
  refine ⟨htree, ?_⟩
  rw [List.toFinset_card_of_nodup hdropPath.support_nodup, p.dropLast.length_support,
    Walk.dropLast, Walk.take_length]
  omega

omit [Fintype α] [DecidableEq α] in
/-- If a cycle realizes the girth and has length at least five, a vertex outside its support has
at most one neighbor on the cycle.  This is the attachment theorem used by L7. -/
theorem Walk.IsCycle.outside_neighbor_unique_of_length_eq_girth_splice
    {v a b x : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth)
    (hx : x ∉ c.support) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  let r : G.Walk a a := c.rotate ha
  have hrCycle : r.IsCycle := hc.rotate ha
  have hbR : b ∈ r.support := (c.mem_support_rotate_iff ha).2 hb
  have hxR : x ∉ r.support := fun hxmem => hx ((c.mem_support_rotate_iff ha).1 hxmem)
  let p : G.Walk a b := r.takeUntil b hbR
  let q : G.Walk b a := r.dropUntil b hbR
  have hpPath : p.IsPath := hrCycle.isPath_takeUntil hbR
  have hqPath : q.IsPath := by
    apply Walk.IsCycle.isPath_of_append_right (p := p) (q := q) (Walk.not_nil_of_ne hab)
    simpa [p, q] using hrCycle
  have hxP : x ∉ p.support := fun hxmem => hxR (r.support_takeUntil_subset hbR hxmem)
  have hxQ : x ∉ q.support := fun hxmem => hxR (r.support_dropUntil_subset hbR hxmem)
  have hpCycle : ((p.concat hxb.symm).concat hxa).IsCycle :=
    hpPath.concat_two_isCycle_splice hab hxP hxb.symm hxa
  have hqCycle : ((q.concat hxa.symm).concat hxb).IsCycle :=
    hqPath.concat_two_isCycle_splice (Ne.symm hab) hxQ hxa.symm hxb
  have hpBound : G.girth ≤ p.length + 2 := by
    simpa only [Walk.length_concat] using G.girth_le_length hpCycle
  have hqBound : G.girth ≤ q.length + 2 := by
    simpa only [Walk.length_concat] using G.girth_le_length hqCycle
  have hrLength : r.length = c.length := by
    dsimp [r, Walk.rotate]
    rw [Walk.length_append, add_comm, ← Walk.length_append, c.take_spec ha]
  have hsplit : p.length + q.length = G.girth := by
    have h0 := congrArg Walk.length (r.take_spec hbR)
    have h1 : p.length + q.length = r.length := by
      simpa only [Walk.length_append, p, q] using h0
    omega
  omega

/-- A nontrivial nearest descent to a shortest cycle has exactly one ordered attachment edge:
its penultimate vertex to its endpoint on the cycle. -/
lemma Walk.nearest_cycle_dropLast_unique_attachment
    {z ku u : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (hku : ku ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hpos : 0 < p.length) :
    p.penultimate ∈ p.dropLast.support.toFinset ∧
      ku ∈ c.support.toFinset ∧ G.Adj p.penultimate ku ∧
      ∀ ⦃x y : α⦄, x ∈ p.dropLast.support.toFinset → y ∈ c.support.toFinset →
        G.Adj x y → x = p.penultimate ∧ y = ku := by
  have hpNotNil : ¬p.Nil := by simpa [Walk.not_nil_iff_lt_length] using hpos
  have hpenAdj : G.Adj p.penultimate ku := p.adj_penultimate hpNotNil
  refine ⟨by simp [Walk.dropLast],
    by simpa using hku, hpenAdj, ?_⟩
  intro x y hx hy hxy
  have hxSupp : x ∈ p.dropLast.support := by simpa using hx
  obtain ⟨j, hj, hjx⟩ := Walk.mem_support_iff_exists_getVert.mp hxSupp
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjLe : j ≤ p.length - 1 := by simpa [hdropLen] using hjx
  have htakeVert : p.getVert j = x := by
    have h0 : p.dropLast.getVert j = x := hj
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
  have hdepth := p.distToSet_getVert_eq_length_sub_of_nearest
    (G := G) hconn (by simpa using hku) hp (Nat.le_trans hjLe (Nat.sub_le _ _))
  have hySet : y ∈ (c.support.toFinset : Set α) := by simpa using hy
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) (p.getVert j) hySet
  have hdistOne : G.dist (p.getVert j) y = 1 := by
    apply dist_eq_one_iff_adj.mpr
    simpa [htakeVert] using hxy
  rw [hdepth, hdistOne] at hsetLe
  have hjEq : j = p.length - 1 := by omega
  have hxEq : x = p.penultimate := by
    rw [← htakeVert, hjEq]
  have hpenOutside : p.penultimate ∉ c.support := by
    have hnot := p.getVert_not_mem_of_length_eq_distToSet hp (i := p.length - 1) (by omega)
    simpa using hnot
  refine ⟨hxEq, ?_⟩
  apply Eq.symm
  apply hc.outside_neighbor_unique_of_length_eq_girth_splice hcLength hg hpenOutside hku
    (by simpa using hy) hpenAdj
  simpa [hxEq] using hxy

omit [Fintype α] [DecidableEq α] in
/-- For a nonnil walk, the support of `dropLast` is the list support with its endpoint removed. -/
lemma Walk.support_dropLast_eq_support_dropLast {u v : α} (p : G.Walk u v)
    (hpos : 0 < p.length) : p.dropLast.support = p.support.dropLast := by
  rw [Walk.dropLast, Walk.take_support_eq_support_take_succ, List.dropLast_eq_take,
    p.length_support]
  congr 1
  omega

omit [Fintype α] [DecidableEq α] in
/-- Every support vertex other than the endpoint lies in the support of `dropLast`. -/
lemma Walk.mem_dropLast_support_of_mem_support_of_ne_end
    {u v x : α} (p : G.Walk u v) (hpos : 0 < p.length)
    (hx : x ∈ p.support) (hxv : x ≠ v) : x ∈ p.dropLast.support := by
  rw [p.support_dropLast_eq_support_dropLast hpos]
  apply List.mem_dropLast_of_mem_of_ne_getLast hx
  simpa using hxv

/-- Erasing the endpoint of a nearest cycle descent removes every attachment of its outside
vertex set to the retained cycle base. -/
lemma Walk.nearest_cycle_dropLast_no_adj_erase_endpoint
    {z ku u : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (hku : ku ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hpos : 0 < p.length) :
    ∀ ⦃x y : α⦄, x ∈ p.dropLast.support.toFinset →
      y ∈ c.support.toFinset.erase ku → ¬G.Adj x y := by
  obtain ⟨_, _, _, huniq⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn p hku hp hpos
  intro x y hx hy hxy
  have hyCycle : y ∈ c.support.toFinset := Finset.mem_of_mem_erase hy
  have hyNe : y ≠ ku := Finset.ne_of_mem_erase hy
  exact hyNe (huniq hx hyCycle hxy).2

/-- A reversed descent prefix ending at depth at least two sends no edge to the cycle. -/
lemma Walk.reverse_take_no_cycle_attachment_of_succ_lt_length
    {z v kv : α} {c : G.Walk z z} (hconn : G.Connected)
    (q : G.Walk v kv) (hkv : kv ∈ c.support)
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    {i : ℕ} (hi : i + 1 < q.length) :
    ∀ ⦃x y : α⦄, x ∈ (q.take i).reverse.support → y ∈ c.support.toFinset →
      ¬G.Adj x y := by
  intro x y hx hy hxy
  obtain ⟨j, hjLe, hjx⟩ :=
    q.exists_index_le_of_mem_support_reverse_take (Nat.le_of_lt (lt_trans (Nat.lt_succ_self i) hi)) hx
  have hdepth := q.distToSet_getVert_eq_length_sub_of_nearest hconn
    (by simpa using hkv) hq (Nat.le_trans hjLe (by omega))
  have hySet : y ∈ (c.support.toFinset : Set α) := by simpa using hy
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) (q.getVert j) hySet
  have hdistOne : G.dist (q.getVert j) y = 1 := by
    apply dist_eq_one_iff_adj.mpr
    simpa [hjx] using hxy
  rw [hdepth, hdistOne] at hsetLe
  omega

omit [DecidableEq α] in
/-- The reversed prefix of a nearest descent is a chordless path. -/
lemma Walk.reverse_take_isPath_and_chordless_of_nearest
    {S : Set α} {v kv : α} (q : G.Walk v kv) (hkv : kv ∈ S)
    (hq : q.length = G.distToSet v S) {i : ℕ} :
    (q.take i).reverse.IsPath ∧
      ∀ ⦃x y : α⦄, x ∈ (q.take i).reverse.support →
        y ∈ (q.take i).reverse.support → G.Adj x y →
          s(x, y) ∈ (q.take i).reverse.edges := by
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) v hkv
  have hdistLe : G.dist v kv ≤ q.length := G.dist_le q
  have hqGeod : q.length = G.dist v kv := by omega
  have htakeGeod : (q.take i).length = G.dist v (q.getVert i) :=
    length_eq_dist_of_subwalk hqGeod (Walk.isSubwalk_take q i)
  have hrevGeod : (q.take i).reverse.length = G.dist (q.getVert i) v := by
    rw [Walk.length_reverse, G.dist_comm]
    exact htakeGeod
  refine ⟨(q.take i).reverse.isPath_of_length_eq_dist hrevGeod, ?_⟩
  intro x y hx hy hxy
  exact (q.take i).reverse.chordless_of_length_eq_dist hrevGeod hx hy hxy

/-- Once a cycle vertex `eraseRoot` is known to preserve the first descent's attachment and remove
all attachments of the reversed prefix, the first-interaction construction instantiates the full
local splice certificate. -/
lemma Walk.interacting_descents_splice_certificate_of_safe_root
    {z u ku v kv eraseRoot : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) {i : ℕ} (hi : i < q.length)
    (hint : InteractsFinset G p.dropLast.support.toFinset (q.getVert i))
    (hfirst : ∀ j : ℕ, j < i →
      ¬InteractsFinset G p.dropLast.support.toFinset (q.getVert j))
    (hvNot : v ∉ p.dropLast.support.toFinset)
    (heraseNe : eraseRoot ≠ ku)
    (htailSafe : ∀ ⦃x y : α⦄, x ∈ (q.take i).reverse.support →
      y ∈ c.support.toFinset.erase eraseRoot → ¬G.Adj x y) :
    (G.induce ((p.dropLast.support.toFinset ∪
      (q.take i).reverse.support.toFinset : Finset α) : Set α)).IsTree ∧
      (∃! e : α × α,
        e.1 ∈ p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset ∧
        e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2) ∧
      G.dist u v + 1 ≤
        (p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset).card := by
  let A := p.dropLast.support.toFinset
  let tail := (q.take i).reverse
  have hselNotA := q.getVert_first_interaction_not_mem A hi hfirst hvNot
  rcases hint with hselA | ⟨r, hrA, hir⟩
  · exact (hselNotA hselA).elim
  have hselNotCycle := q.getVert_not_mem_of_length_eq_distToSet hq hi
  have hselNeKu : q.getVert i ≠ ku := by
    intro heq
    apply hselNotCycle
    simpa [heq] using hku
  have hselNotP : q.getVert i ∉ p.support := by
    intro hmem
    apply hselNotA
    have hdrop := p.mem_dropLast_support_of_mem_support_of_ne_end hpPos hmem hselNeKu
    simpa [A] using hdrop
  have hA_sub {x : α} (hx : x ∈ A) : x ∈ p.support := by
    have hxDrop : x ∈ p.dropLast.support := by simpa [A] using hx
    exact (Walk.isSubwalk_take p (p.length - 1)).support_subset hxDrop
  have hruniq : ∀ ⦃y : α⦄, y ∈ A → G.Adj (q.getVert i) y → y = r := by
    intro y hy hiy
    exact p.nearest_descents_selected_neighbor_unique hconn q
      (by simpa using hku) (by simpa using hkv) hp hq hi hselNotP
      (hA_sub hy) (hA_sub hrA) hiy hir hg
  obtain ⟨htailDisj, hcross⟩ :=
    q.reverse_take_disjoint_and_unique_cross_of_first A hi hfirst hvNot hruniq
  obtain ⟨hATree, hAcard⟩ := p.nearest_descent_dropLast_tree_and_card
    (by simpa using hku) hp hpPos
  obtain ⟨htailPath, htailChordless⟩ :=
    q.reverse_take_isPath_and_chordless_of_nearest (by simpa using hkv) hq
  obtain ⟨hpenA, hkuCycle, hpenAdj, hbaseUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn p hku hp hpPos
  have hkuRet : ku ∈ c.support.toFinset.erase eraseRoot := by
    exact Finset.mem_erase.mpr ⟨Ne.symm heraseNe, hkuCycle⟩
  have hbaseRet : ∀ ⦃x y : α⦄, x ∈ A →
      y ∈ c.support.toFinset.erase eraseRoot → G.Adj x y →
      x = p.penultimate ∧ y = ku := by
    intro x y hx hy hxy
    exact hbaseUnique (by simpa [A] using hx) (Finset.mem_of_mem_erase hy) hxy
  have hrDrop : r ∈ p.dropLast.support := by simpa [A] using hrA
  obtain ⟨jr, hjr, hjrLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hrDrop
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjrLe : jr ≤ p.length - 1 := by simpa [hdropLen] using hjrLeDrop
  have hjrP : p.getVert jr = r := by
    have h0 : p.dropLast.getVert jr = r := hjr
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjrLe] using h0
  have hir' : G.Adj (p.getVert jr) (q.getVert i) := by simpa [hjrP] using hir.symm
  let connector : G.Walk u v := ((p.take jr).concat hir').append tail
  have hconnectorLen : connector.length = jr + 1 + i := by
    dsimp [connector, tail]
    rw [Walk.length_append, Walk.length_concat, Walk.length_reverse,
      Walk.take_length, Walk.take_length, Nat.min_eq_left (Nat.le_trans hjrLe (Nat.sub_le _ _)),
      Nat.min_eq_left (Nat.le_of_lt hi)]
  have hdistConnector : G.dist u v ≤ jr + 1 + i := by
    calc
      G.dist u v ≤ connector.length := G.dist_le connector
      _ = jr + 1 + i := hconnectorLen
  have htailLength : tail.length = q.length - (q.length - i) := by
    dsimp [tail]
    rw [Walk.length_reverse, Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hnuPos : 1 ≤ p.length - jr := by omega
  have hnuLe : p.length - jr ≤ p.length := Nat.sub_le _ _
  have hmetric : G.dist u v ≤
      (p.length - (p.length - jr)) + 1 + (q.length - (q.length - i)) := by
    omega
  exact Walk.IsPath.interacting_descent_splice_certificate tail htailPath hATree
    htailDisj htailChordless hrA hir hcross hpenA hkuRet hpenAdj hbaseRet
    htailSafe hAcard htailLength hnuPos hnuLe hmetric

/-- If the penultimate vertices of two nearest-cycle descents are joined across the descents, and
the second penultimate is outside the first descent, then their cycle endpoints are distinct. -/
lemma Walk.nearest_cycle_crossed_penultimate_endpoints_ne
    {z u ku v kv r : α} {c : G.Walk z z} (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hr : r ∈ p.dropLast.support) (hqr : G.Adj q.penultimate r)
    (hout : q.penultimate ∉ p.support) : kv ≠ ku := by
  have hkuSet : ku ∈ (c.support.toFinset : Set α) := by simpa using hku
  have hkvSet : kv ∈ (c.support.toFinset : Set α) := by simpa using hkv
  have hsetLe := distToSet_le_dist_of_mem_public (G := G) u hkuSet
  have hpDistLe : G.dist u ku ≤ p.length := G.dist_le p
  have hpGeod : p.length = G.dist u ku := by omega
  have hpPath := p.isPath_of_length_eq_dist hpGeod
  obtain ⟨jr, hjr, hjrLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hr
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjrLe : jr ≤ p.length - 1 := by simpa [hdropLen] using hjrLeDrop
  have hjrP : p.getVert jr = r := by
    have h0 : p.dropLast.getVert jr = r := hjr
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjrLe] using h0
  have hqDepth := q.distToSet_getVert_eq_length_sub_of_nearest hconn
    hkvSet hq (i := q.length - 1) (Nat.sub_le _ _)
  have hpDepth := p.distToSet_getVert_eq_length_sub_of_nearest hconn
    hkuSet hp (Nat.le_trans hjrLe (Nat.sub_le _ _))
  have hdepthLe := distToSet_le_add_one_of_adj (G := G)
    ⟨ku, hkuSet⟩ hqr.symm
  rw [← hjrP, hqDepth, hpDepth] at hdepthLe
  have hspan : p.length - jr ≤ 2 := by omega
  let r0 := p.drop jr
  have hr0Path : r0.IsPath := isPath_of_isSubwalk (Walk.isSubwalk_drop p jr) hpPath
  let path : G.Walk r ku := r0.copy hjrP rfl
  have hpath : path.IsPath := (Walk.isPath_copy r0 hjrP rfl).2 hr0Path
  have hpathLen : path.length ≤ 2 := by
    dsimp [path, r0]
    rw [Walk.length_copy, Walk.drop_length]
    exact hspan
  have hpathOut : q.penultimate ∉ path.support := by
    intro hmem
    apply hout
    apply (Walk.isSubwalk_drop p jr).support_subset
    dsimp [path, r0] at hmem
    rw [Walk.support_copy] at hmem
    exact hmem
  intro hkvku
  have hqNotNil : ¬q.Nil := by simpa [Walk.not_nil_iff_lt_length] using hqPos
  have hqku : G.Adj q.penultimate ku := by
    simpa [hkvku] using q.adj_penultimate hqNotNil
  have hrku := hpath.outside_neighbor_unique_of_length_le_two hpathLen hpathOut hqr hqku hg
  have heqVert : p.getVert jr = p.getVert p.length := by
    rw [p.getVert_length, hjrP]
    exact hrku
  have hindexEq : jr = p.length :=
    hpPath.getVert_injOn (by simp; omega) (by simp) heqVert
  omega

omit [Fintype α] [DecidableEq α] in
/-- Every vertex of a cycle has a distinct second cycle vertex. -/
lemma Walk.IsCycle.exists_support_ne {z a : α} {c : G.Walk z z}
    (hc : c.IsCycle) (ha : a ∈ c.support) : ∃ b ∈ c.support, b ≠ a := by
  let r : G.Walk a a := c.rotate ha
  have hrCycle : r.IsCycle := hc.rotate ha
  have hbR : r.snd ∈ r.support := r.getVert_mem_support 1
  have hbC : r.snd ∈ c.support := (c.mem_support_rotate_iff ha).1 hbR
  exact ⟨r.snd, hbC, (r.adj_snd hrCycle.not_nil).ne.symm⟩

/-- Full interacting-descent Case B of L7: when the top of the second descent is outside the
first descent, a first interacting index and a cycle vertex to erase produce the exact induced-tree,
one-attachment, and distance-size certificate. -/
lemma Walk.interacting_descents_splice_caseB
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hvNot : v ∉ p.dropLast.support.toFinset)
    (hex : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)) :
    ∃ i : ℕ, ∃ eraseRoot : α,
      i < q.length ∧ eraseRoot ∈ c.support ∧ eraseRoot ≠ ku ∧
      (G.induce ((p.dropLast.support.toFinset ∪
        (q.take i).reverse.support.toFinset : Finset α) : Set α)).IsTree ∧
      (∃! e : α × α,
        e.1 ∈ p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset ∧
        e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2) ∧
      G.dist u v + 1 ≤
        (p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset).card := by
  obtain ⟨i, hi, hint, hfirst⟩ :=
    q.exists_first_interaction_index p.dropLast.support.toFinset hex
  by_cases hdeep : i + 1 < q.length
  · obtain ⟨eraseRoot, heraseMem, heraseNe⟩ := hc.exists_support_ne hku
    have htailFull := Walk.reverse_take_no_cycle_attachment_of_succ_lt_length
      hconn q hkv hq hdeep
    have htailSafe : ∀ ⦃x y : α⦄, x ∈ (q.take i).reverse.support →
        y ∈ c.support.toFinset.erase eraseRoot → ¬G.Adj x y := by
      intro x y hx hy
      exact htailFull hx (Finset.mem_of_mem_erase hy)
    refine ⟨i, eraseRoot, hi, heraseMem, heraseNe, ?_⟩
    exact Walk.interacting_descents_splice_certificate_of_safe_root hc hcLength hg hconn
      p q hku hkv hp hq hpPos hi hint hfirst hvNot heraseNe htailSafe
  · have hiEq : i = q.length - 1 := by omega
    let A := p.dropLast.support.toFinset
    have hselNotA := q.getVert_first_interaction_not_mem A hi hfirst hvNot
    rcases hint with hselA | ⟨r, hrA, hir⟩
    · exact (hselNotA hselA).elim
    have hselNotCycle := q.getVert_not_mem_of_length_eq_distToSet hq hi
    have hselNeKu : q.getVert i ≠ ku := by
      intro heq
      apply hselNotCycle
      simpa [heq] using hku
    have hselNotP : q.getVert i ∉ p.support := by
      intro hmem
      apply hselNotA
      have hdrop := p.mem_dropLast_support_of_mem_support_of_ne_end hpPos hmem hselNeKu
      simpa [A] using hdrop
    have hpenEq : q.getVert i = q.penultimate := by rw [hiEq]
    have hrDrop : r ∈ p.dropLast.support := by simpa [A] using hrA
    have hirPen : G.Adj q.penultimate r := by simpa [← hpenEq] using hir
    have houtPen : q.penultimate ∉ p.support := by simpa [← hpenEq] using hselNotP
    have hkvNe := Walk.nearest_cycle_crossed_penultimate_endpoints_ne hg hconn p q hku hkv
      hp hq hpPos hqPos hrDrop hirPen houtPen
    have hqErase := Walk.nearest_cycle_dropLast_no_adj_erase_endpoint hc hcLength hg hconn
      q hkv hq hqPos
    have htailSafe : ∀ ⦃x y : α⦄, x ∈ (q.take i).reverse.support →
        y ∈ c.support.toFinset.erase kv → ¬G.Adj x y := by
      intro x y hx hy
      have hxTake : x ∈ (q.take i).support := by
        rw [Walk.support_reverse] at hx
        simpa using hx
      have hxDrop : x ∈ q.dropLast.support.toFinset := by
        rw [hiEq] at hxTake
        simpa [Walk.dropLast] using hxTake
      exact hqErase hxDrop hy
    refine ⟨i, kv, hi, hkv, hkvNe, ?_⟩
    exact Walk.interacting_descents_splice_certificate_of_safe_root hc hcLength hg hconn
      p q hku hkv hp hq hpPos hi (Or.inr ⟨r, hrA, hir⟩) hfirst hvNot hkvNe htailSafe

/-- Interacting-descent Case A of L7: if the top of the second descent lies on the first descent,
the first descent alone is the required admissible induced tree. -/
lemma Walk.interacting_descents_splice_caseA
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hvA : v ∈ p.dropLast.support.toFinset) :
    ∃ eraseRoot : α, eraseRoot ∈ c.support ∧ eraseRoot ≠ ku ∧
      (G.induce (p.dropLast.support.toFinset : Set α)).IsTree ∧
      (∃! e : α × α, e.1 ∈ p.dropLast.support.toFinset ∧
        e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2) ∧
      G.dist u v + 1 ≤ p.dropLast.support.toFinset.card := by
  obtain ⟨eraseRoot, heraseMem, heraseNe⟩ := hc.exists_support_ne hku
  obtain ⟨hATree, hAcard⟩ := p.nearest_descent_dropLast_tree_and_card
    (by simpa using hku) hp hpPos
  obtain ⟨hpenA, hkuCycle, hpenAdj, hbaseUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn p hku hp hpPos
  have hkuRet : ku ∈ c.support.toFinset.erase eraseRoot :=
    Finset.mem_erase.mpr ⟨Ne.symm heraseNe, hkuCycle⟩
  have hedgeUnique : ∃! e : α × α, e.1 ∈ p.dropLast.support.toFinset ∧
      e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2 := by
    refine ⟨(p.penultimate, ku), ⟨hpenA, hkuRet, hpenAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    have hpair := hbaseUnique hx (Finset.mem_of_mem_erase hy) hxy
    apply Prod.ext
    · exact hpair.1
    · exact hpair.2
  have hvSupp : v ∈ p.dropLast.support := by simpa using hvA
  obtain ⟨j, hj, hjLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hvSupp
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjLe : j ≤ p.length - 1 := by simpa [hdropLen] using hjLeDrop
  have hjP : p.getVert j = v := by
    have h0 : p.dropLast.getVert j = v := hj
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
  have hpDepth := p.distToSet_getVert_eq_length_sub_of_nearest hconn
    (by simpa using hku) hp (Nat.le_trans hjLe (Nat.sub_le _ _))
  rw [hjP, ← hq] at hpDepth
  let pj : G.Walk u v := (p.take j).copy rfl hjP
  have hpjLen : pj.length = (p.take j).length := by
    dsimp [pj]
    rw [Walk.length_copy]
  have hdist : G.dist u v ≤ j := by
    calc
      G.dist u v ≤ pj.length := G.dist_le pj
      _ = (p.take j).length := hpjLen
      _ = j := by rw [Walk.take_length, Nat.min_eq_left (Nat.le_trans hjLe (Nat.sub_le _ _))]
  refine ⟨eraseRoot, heraseMem, heraseNe, hATree, hedgeUnique, ?_⟩
  rw [hAcard]
  omega

/-- Full interacting part L7(b), in the exact one-component form needed by `M(K)`: two nearest
cycle descents that interact yield an admissible induced tree of order at least `dist u v + 1`. -/
lemma Walk.interacting_descents_splice_L7b
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hex : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)) :
    ∃ F : Finset α, ∃ eraseRoot : α,
      eraseRoot ∈ c.support ∧ eraseRoot ≠ ku ∧
      (G.induce (F : Set α)).IsTree ∧
      (∃! e : α × α, e.1 ∈ F ∧
        e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2) ∧
      G.dist u v + 1 ≤ F.card := by
  by_cases hvA : v ∈ p.dropLast.support.toFinset
  · obtain ⟨eraseRoot, hrMem, hrNe, htree, hedge, hcard⟩ :=
      Walk.interacting_descents_splice_caseA hc hcLength hg hconn p q hku
        hp hq hpPos hqPos hvA
    exact ⟨p.dropLast.support.toFinset, eraseRoot, hrMem, hrNe, htree, hedge, hcard⟩
  · obtain ⟨i, eraseRoot, hi, hrMem, hrNe, htree, hedge, hcard⟩ :=
      Walk.interacting_descents_splice_caseB hc hcLength hg hconn p q hku hkv
        hp hq hpPos hqPos hvA hex
    exact ⟨p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset,
      eraseRoot, hrMem, hrNe, htree, hedge, hcard⟩

/-- The outside part of a nearest descent is disjoint from the target set. -/
lemma Walk.nearest_descent_dropLast_disjoint_target
    {S : Set α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.distToSet u S) (hpos : 0 < p.length) :
    Disjoint p.dropLast.support.toFinset S.toFinset := by
  rw [Finset.disjoint_left]
  intro x hx hS
  have hxSupp : x ∈ p.dropLast.support := by simpa using hx
  obtain ⟨j, hj, hjLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hxSupp
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjLe : j ≤ p.length - 1 := by simpa [hdropLen] using hjLeDrop
  have hjP : p.getVert j = x := by
    have h0 : p.dropLast.getVert j = x := hj
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
  have hnot := p.getVert_not_mem_of_length_eq_distToSet hp (i := j) (by omega)
  apply hnot
  rw [hjP]
  exact Set.mem_toFinset.mp hS

/-- A reversed prefix ending before a nearest descent's target endpoint is disjoint from the
target set. -/
lemma Walk.reverse_take_disjoint_target_of_nearest
    {S : Set α} {u v : α} (q : G.Walk u v)
    (hq : q.length = G.distToSet u S) {i : ℕ} (hi : i < q.length) :
    Disjoint (q.take i).reverse.support.toFinset S.toFinset := by
  rw [Finset.disjoint_left]
  intro x hx hS
  have hxSupp : x ∈ (q.take i).reverse.support := by simpa using hx
  obtain ⟨j, hjLe, hjx⟩ :=
    q.exists_index_le_of_mem_support_reverse_take (Nat.le_of_lt hi) hxSupp
  have hnot := q.getVert_not_mem_of_length_eq_distToSet hq (i := j) (by omega)
  apply hnot
  rw [hjx]
  exact Set.mem_toFinset.mp hS

/-- L7(b) with the explicit `F ∩ K = ∅` condition required by the definition of `M(K)`. -/
lemma Walk.interacting_descents_splice_L7b_outside_cycle
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hex : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)) :
    ∃ F : Finset α, ∃ eraseRoot : α,
      eraseRoot ∈ c.support ∧ eraseRoot ≠ ku ∧
      Disjoint F c.support.toFinset ∧
      (G.induce (F : Set α)).IsTree ∧
      (∃! e : α × α, e.1 ∈ F ∧
        e.2 ∈ c.support.toFinset.erase eraseRoot ∧ G.Adj e.1 e.2) ∧
      G.dist u v + 1 ≤ F.card := by
  have hpDisj : Disjoint p.dropLast.support.toFinset c.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hcX
    have hxSupp : x ∈ p.dropLast.support := by simpa using hx
    obtain ⟨j, hj, hjLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hxSupp
    have hdropLen : p.dropLast.length = p.length - 1 := by
      simp only [Walk.dropLast, Walk.take_length]
      omega
    have hjLe : j ≤ p.length - 1 := by simpa [hdropLen] using hjLeDrop
    have hjP : p.getVert j = x := by
      have h0 : p.dropLast.getVert j = x := hj
      simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
    have hnot := p.getVert_not_mem_of_length_eq_distToSet hp (i := j) (by omega)
    apply hnot
    rw [hjP]
    exact hcX
  by_cases hvA : v ∈ p.dropLast.support.toFinset
  · obtain ⟨eraseRoot, hrMem, hrNe, htree, hedge, hcard⟩ :=
      Walk.interacting_descents_splice_caseA hc hcLength hg hconn p q hku
        hp hq hpPos hqPos hvA
    exact ⟨p.dropLast.support.toFinset, eraseRoot, hrMem, hrNe, hpDisj,
      htree, hedge, hcard⟩
  · obtain ⟨i, eraseRoot, hi, hrMem, hrNe, htree, hedge, hcard⟩ :=
      Walk.interacting_descents_splice_caseB hc hcLength hg hconn p q hku hkv
        hp hq hpPos hqPos hvA hex
    have hqDisj :
        Disjoint (q.take i).reverse.support.toFinset c.support.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hcX
      have hxSupp : x ∈ (q.take i).reverse.support := by simpa using hx
      obtain ⟨j, hjLe, hjx⟩ :=
        q.exists_index_le_of_mem_support_reverse_take (Nat.le_of_lt hi) hxSupp
      have hnot := q.getVert_not_mem_of_length_eq_distToSet hq (i := j) (by omega)
      apply hnot
      rw [hjx]
      exact hcX
    have hUnionDisj : Disjoint
        (p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset)
        c.support.toFinset := by
      rw [Finset.disjoint_union_left]
      exact ⟨hpDisj, hqDisj⟩
    exact ⟨p.dropLast.support.toFinset ∪ (q.take i).reverse.support.toFinset,
      eraseRoot, hrMem, hrNe, hUnionDisj, htree, hedge, hcard⟩
omit [Fintype α] [DecidableEq α] in
/-- Every support vertex of a cycle occurs at an index strictly below its length. -/
lemma Walk.IsCycle.exists_index_lt_getVert_splice
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle) (hx : x ∈ c.support) :
    ∃ i : ℕ, i < c.length ∧ c.getVert i = x := by
  obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hiLt : i < c.length
  · exact ⟨i, hiLt, hiEq⟩
  have hiLen : i = c.length := by omega
  have hpos : 0 < c.length := by
    have := hc.three_le_length
    omega
  refine ⟨0, hpos, ?_⟩
  calc
    c.getVert 0 = z := by simp
    _ = c.getVert c.length := by simp
    _ = x := by simpa [hiLen] using hiEq

omit [Fintype α] [DecidableEq α] in
/-- The sum of the three pairwise graph distances between vertices on one cycle
is at most the length of that cycle. -/
lemma Walk.IsCycle.sum_three_dist_le_length_splice
    {z a b d : α} {c : G.Walk z z} (hc : c.IsCycle)
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hd : d ∈ c.support) :
    G.dist a b + G.dist a d + G.dist b d ≤ c.length := by
  obtain ⟨i, hiLt, hi⟩ := hc.exists_index_lt_getVert_splice ha
  obtain ⟨j, hjLt, hj⟩ := hc.exists_index_lt_getVert_splice hb
  obtain ⟨k, hkLt, hk⟩ := hc.exists_index_lt_getVert_splice hd
  have key : ∀ {i j k : ℕ} {a b d : α},
      i < c.length → j < c.length → k < c.length →
      c.getVert i = a → c.getVert j = b → c.getVert k = d →
      i ≤ j → j ≤ k →
      G.dist a b + G.dist a d + G.dist b d ≤ c.length := by
    intro i j k a b d hiLt hjLt hkLt hi hj hk hij hjk
    have hab0 := G.dist_le ((c.drop i).take (j - i))
    have hab : G.dist a b ≤ j - i := by
      simpa [Walk.drop_getVert, Nat.add_sub_of_le hij, hi, hj,
        Walk.take_length, Walk.drop_length,
        Nat.min_eq_left (by omega : j - i ≤ c.length - i)] using hab0
    have hbd0 := G.dist_le ((c.drop j).take (k - j))
    have hbd : G.dist b d ≤ k - j := by
      simpa [Walk.drop_getVert, Nat.add_sub_of_le hjk, hj, hk,
        Walk.take_length, Walk.drop_length,
        Nat.min_eq_left (by omega : k - j ≤ c.length - j)] using hbd0
    have hda0 := G.dist_le ((c.drop k).append (c.take i))
    have hda : G.dist a d ≤ c.length - k + i := by
      have h0 : G.dist d a ≤ c.length - k + i := by
        simpa [Walk.length_append, Walk.drop_length, Walk.take_length,
          Nat.min_eq_left (Nat.le_of_lt hiLt), hi, hk] using hda0
      simpa only [G.dist_comm] using h0
    omega
  rcases le_total i j with hij | hji
  · rcases le_total j k with hjk | hkj
    · exact key hiLt hjLt hkLt hi hj hk hij hjk
    · rcases le_total i k with hik | hki
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hiLt hkLt hjLt hi hk hj hik hkj
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hkLt hiLt hjLt hk hi hj hki hij
  · rcases le_total i k with hik | hki
    · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
        key hjLt hiLt hkLt hj hi hk hji hik
    · rcases le_total j k with hjk | hkj
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hjLt hkLt hiLt hj hk hi hjk hki
      · simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using
          key hkLt hjLt hiLt hk hj hi hkj hji
omit [Fintype α] [DecidableEq α] in
/-- L6: lifting three roots on a cycle through three terminal-to-root walks. -/
lemma Walk.IsCycle.three_arc_inequality_splice
    {z u a v b w d : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hconn : G.Connected)
    (p : G.Walk u a) (q : G.Walk v b) (t : G.Walk w d)
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hd : d ∈ c.support) :
    G.dist u v + G.dist u w + G.dist v w ≤
      2 * (p.length + q.length + t.length) + c.length := by
  have hroot := hc.sum_three_dist_le_length_splice ha hb hd
  have hua : G.dist u a ≤ p.length := G.dist_le p
  have hvb : G.dist v b ≤ q.length := G.dist_le q
  have hwd : G.dist w d ≤ t.length := G.dist_le t
  have hbv : G.dist b v ≤ q.length := by
    simpa only [G.dist_comm] using hvb
  have hdw : G.dist d w ≤ t.length := by
    simpa only [G.dist_comm] using hwd
  have hav : G.dist a v ≤ G.dist a b + G.dist b v :=
    hconn.dist_triangle
  have hadw : G.dist a w ≤ G.dist a d + G.dist d w :=
    hconn.dist_triangle
  have hbdw : G.dist b w ≤ G.dist b d + G.dist d w :=
    hconn.dist_triangle
  have huv : G.dist u v ≤ p.length + G.dist a b + q.length := by
    have h := hconn.dist_triangle (u := u) (v := a) (w := v)
    omega
  have huw : G.dist u w ≤ p.length + G.dist a d + t.length := by
    have h := hconn.dist_triangle (u := u) (v := a) (w := w)
    omega
  have hvw : G.dist v w ≤ q.length + G.dist b d + t.length := by
    have h := hconn.dist_triangle (u := v) (v := b) (w := w)
    omega
  omega
omit [Fintype α] in
/-- A girth cycle has one distinct support vertex per edge. -/
lemma Walk.IsCycle.card_support_toFinset_eq_length_splice
    {v : α} {c : G.Walk v v} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hvTail : v ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  have hfin : c.support.toFinset = c.support.tail.toFinset := by
    rw [c.support_eq_cons, List.toFinset_cons]
    exact Finset.insert_eq_of_mem (by simpa using hvTail)
  rw [hfin, List.toFinset_card_of_nodup hc.support_nodup, List.length_tail,
    c.length_support]
  omega

omit [Fintype α] in
/-- On a girth cycle of length at least five, a root can avoid two prescribed
cycle vertices. -/
lemma Walk.IsCycle.exists_support_ne_two_splice
    {v a b : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) :
    ∃ root ∈ c.support, root ≠ a ∧ root ≠ b := by
  by_contra hno
  have hsub : c.support.toFinset ⊆ ({a, b} : Finset α) := by
    intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    exfalso
    apply hno
    exact ⟨x, by simpa using hx, hxa, hxb⟩
  have hcardLe := Finset.card_le_card hsub
  have hpairCard : ({a, b} : Finset α).card ≤ 2 := by
    calc
      ({a, b} : Finset α).card ≤ ({b} : Finset α).card + 1 :=
        Finset.card_insert_le a {b}
      _ = 2 := by rw [Finset.card_singleton]
  rw [hc.card_support_toFinset_eq_length_splice, hcLength] at hcardLe
  omega

omit [Fintype α] in
/-- On a girth cycle of length at least five, a root can avoid three prescribed
cycle vertices. -/
lemma Walk.IsCycle.exists_support_ne_three_splice
    {v a b d : α} {c : G.Walk v v} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) :
    ∃ root ∈ c.support, root ≠ a ∧ root ≠ b ∧ root ≠ d := by
  by_contra hno
  have hsub : c.support.toFinset ⊆ ({a, b, d} : Finset α) := by
    intro x hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    by_cases hxd : x = d
    · simp [hxd]
    exfalso
    apply hno
    exact ⟨x, by simpa using hx, hxa, hxb, hxd⟩
  have hcardLe := Finset.card_le_card hsub
  have htripleCard : ({a, b, d} : Finset α).card ≤ 3 := by
    calc
      ({a, b, d} : Finset α).card ≤ ({b, d} : Finset α).card + 1 :=
        Finset.card_insert_le a {b, d}
      _ ≤ (({d} : Finset α).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le b {d}) 1
      _ = 3 := by rw [Finset.card_singleton]
  rw [hc.card_support_toFinset_eq_length_splice, hcLength] at hcardLe
  omega
/-- The outside portion of a nearest descent is disjoint from a finite target
without passing through `Set.toFinset` instance choices. -/
lemma Walk.nearest_descent_dropLast_disjoint_finset_target
    {K : Finset α} {u v : α} (p : G.Walk u v)
    (hp : p.length = G.distToSet u (K : Set α)) (hpos : 0 < p.length) :
    Disjoint p.dropLast.support.toFinset K := by
  rw [Finset.disjoint_left]
  intro x hx hK
  have hxSupp : x ∈ p.dropLast.support := by simpa using hx
  obtain ⟨j, hj, hjLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hxSupp
  have hdropLen : p.dropLast.length = p.length - 1 := by
    simp only [Walk.dropLast, Walk.take_length]
    omega
  have hjLe : j ≤ p.length - 1 := by simpa [hdropLen] using hjLeDrop
  have hjP : p.getVert j = x := by
    have h0 : p.dropLast.getVert j = x := hj
    simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
  have hnot := p.getVert_not_mem_of_length_eq_distToSet hp (i := j) (by omega)
  apply hnot
  rw [hjP]
  exact hK
omit [Fintype α] in
/-- If no strict descent index interacts with `A`, then the positive outside path is
disjoint and nonadjacent to `A`. -/
lemma Walk.dropLast_disjoint_and_nonadjacent_of_no_interaction_index
    {v kv : α} (q : G.Walk v kv) (A : Finset α) (hqPos : 0 < q.length)
    (hno : ¬∃ i : ℕ, i < q.length ∧ InteractsFinset G A (q.getVert i)) :
    Disjoint A q.dropLast.support.toFinset ∧
      ∀ ⦃x y : α⦄, x ∈ A → y ∈ q.dropLast.support.toFinset → ¬G.Adj x y := by
  have hnot : ∀ ⦃y : α⦄, y ∈ q.dropLast.support.toFinset →
      ¬InteractsFinset G A y := by
    intro y hyQ hinter
    have hySupp : y ∈ q.dropLast.support := by simpa using hyQ
    obtain ⟨j, hj, hjLeDrop⟩ := Walk.mem_support_iff_exists_getVert.mp hySupp
    have hdropLen : q.dropLast.length = q.length - 1 := by
      simp only [Walk.dropLast, Walk.take_length]
      omega
    have hjLe : j ≤ q.length - 1 := by simpa [hdropLen] using hjLeDrop
    have hjQ : q.getVert j = y := by
      have h0 : q.dropLast.getVert j = y := hj
      simpa [Walk.dropLast, Walk.take_getVert, Nat.min_eq_right hjLe] using h0
    apply hno
    exact ⟨j, by omega, by simpa [hjQ] using hinter⟩
  constructor
  · rw [Finset.disjoint_left]
    intro x hxA hxQ
    exact (hnot hxQ) (Or.inl hxA)
  · intro x y hxA hyQ hxy
    exact (hnot hyQ) (Or.inr ⟨x, hxA, hxy.symm⟩)

/-- Erasing one vertex from a girth-realizing cycle gives the zero-tail base bound. -/
lemma Walk.IsCycle.girth_sub_one_le_largestInducedTreeSize_splice
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) :
    G.girth - 1 ≤ largestInducedTreeSize G := by
  have hz : z ∈ c.support := c.start_mem_support
  let rot := c.rotate hz
  let base := rot.tail.dropLast
  have hbaseCert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase z ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [rot, base] using
      hc.erase_vertex_path_certificate_splice hz hcLength
  rcases hbaseCert with ⟨_, _, hbaseTree, hbaseCard⟩
  have hle := hbaseTree.card_le_largestInducedTreeSize_splice
  rw [hbaseCard, hcLength] at hle
  exact hle

/-- One positive nearest-cycle descent attached to a retained girth-cycle path
gives an induced tree of order `girth - 1 + descent.length`. -/
lemma Walk.one_descent_largestInducedTreeSize
    {z u ku : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (hku : ku ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) :
    G.girth - 1 + p.length ≤ largestInducedTreeSize G := by
  let P := p.dropLast.support.toFinset
  obtain ⟨eraseRoot, hrMem, hrNeKu⟩ := hc.exists_support_ne hku
  obtain ⟨hPTree, hPcard⟩ := p.nearest_descent_dropLast_tree_and_card
    (by simpa using hku) hp hpPos
  obtain ⟨hpPen, hkuCycle, hpAdj, hpUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      p hku hp hpPos
  let rot := c.rotate hrMem
  let base := rot.tail.dropLast
  have hbaseCert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase eraseRoot ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [rot, base] using
      hc.erase_vertex_path_certificate_splice hrMem hcLength
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, hbaseCard⟩
  have hPcycle : Disjoint P c.support.toFinset := by
    dsimp [P]
    exact p.nearest_descent_dropLast_disjoint_finset_target hp hpPos
  have hPbase : Disjoint P base.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxP hxBase
    apply Finset.disjoint_left.mp hPcycle hxP
    rw [hbaseSupport] at hxBase
    exact Finset.mem_of_mem_erase hxBase
  have hkuBase : ku ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKu.symm, hkuCycle⟩
  have hpCross : ∃! e : α × α,
      e.1 ∈ P ∧ e.2 ∈ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    refine ⟨(p.penultimate, ku), ⟨by simp [P, hpPen], hkuBase, hpAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxP, hyBase, hxy⟩
    have hyCycle : y ∈ c.support.toFinset := by
      rw [hbaseSupport] at hyBase
      exact Finset.mem_of_mem_erase hyBase
    rcases hpUnique (by simpa [P] using hxP) hyCycle hxy with ⟨rfl, rfl⟩
    rfl
  have hUnionTree :
      (G.induce ((P ∪ base.support.toFinset : Finset α) : Set α)).IsTree :=
    hPTree.induce_union_of_disjoint_of_unique_adj_splice
      hbaseTree hPbase hpCross
  have hUnionCard :
      (P ∪ base.support.toFinset).card =
        P.card + base.support.toFinset.card :=
    Finset.card_union_of_disjoint hPbase
  have hsize :
      G.girth - 1 + p.length ≤ (P ∪ base.support.toFinset).card := by
    rw [hUnionCard, show P.card = p.length by simpa [P] using hPcard,
      hbaseCard, hcLength]
    omega
  exact hsize.trans hUnionTree.card_le_largestInducedTreeSize_splice
/-- The noninteracting part L7(a) for two fixed positive nearest-cycle descents:
their two outside paths and the cycle with a safe vertex erased form one induced tree. -/
lemma Walk.noninteracting_descents_L7a_largestInducedTreeSize
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support)
    (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hdisjPQ : Disjoint p.dropLast.support.toFinset
      q.dropLast.support.toFinset)
    (hnoAdjPQ : ∀ ⦃x y : α⦄, x ∈ p.dropLast.support.toFinset →
      y ∈ q.dropLast.support.toFinset → ¬G.Adj x y) :
    G.girth - 1 + p.length + q.length ≤ largestInducedTreeSize G := by
  let P := p.dropLast.support.toFinset
  let Q := q.dropLast.support.toFinset
  obtain ⟨eraseRoot, hrMem, hrNeKu, hrNeKv⟩ :=
    hc.exists_support_ne_two_splice hcLength hg
  obtain ⟨hPTree, hPcard⟩ := p.nearest_descent_dropLast_tree_and_card
    (by simpa using hku) hp hpPos
  obtain ⟨hQTree, hQcard⟩ := q.nearest_descent_dropLast_tree_and_card
    (by simpa using hkv) hq hqPos
  obtain ⟨hpPen, hkuCycle, hpAdj, hpUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      p hku hp hpPos
  obtain ⟨hqPen, hkvCycle, hqAdj, hqUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      q hkv hq hqPos
  let r := c.rotate hrMem
  let base := r.tail.dropLast
  have hbaseCert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase eraseRoot ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [r, base] using
      hc.erase_vertex_path_certificate_splice hrMem hcLength
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, hbaseCard⟩
  have hPcycle : Disjoint P c.support.toFinset := by
    dsimp [P]
    exact p.nearest_descent_dropLast_disjoint_finset_target hp hpPos
  have hQcycle : Disjoint Q c.support.toFinset := by
    dsimp [Q]
    exact q.nearest_descent_dropLast_disjoint_finset_target hq hqPos
  have hPbase : Disjoint P base.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxP hxBase
    apply Finset.disjoint_left.mp hPcycle hxP
    rw [hbaseSupport] at hxBase
    exact Finset.mem_of_mem_erase hxBase
  have hkuBase : ku ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKu.symm, hkuCycle⟩
  have hpCross : ∃! e : α × α,
      e.1 ∈ P ∧ e.2 ∈ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    refine ⟨(p.penultimate, ku), ⟨by simp [P, hpPen], hkuBase, hpAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxP, hyBase, hxy⟩
    have hyCycle : y ∈ c.support.toFinset := by
      rw [hbaseSupport] at hyBase
      exact Finset.mem_of_mem_erase hyBase
    rcases hpUnique (by simpa [P] using hxP) hyCycle hxy with ⟨rfl, rfl⟩
    rfl
  have hUnionP :
      (G.induce ((P ∪ base.support.toFinset : Finset α) : Set α)).IsTree :=
    hPTree.induce_union_of_disjoint_of_unique_adj_splice
      hbaseTree hPbase hpCross
  have hQUnion : Disjoint Q (P ∪ base.support.toFinset) := by
    rw [Finset.disjoint_left]
    intro x hxQ hxUnion
    rcases Finset.mem_union.mp hxUnion with hxP | hxBase
    · exact Finset.disjoint_left.mp hdisjPQ (by simpa [P] using hxP)
        (by simpa [Q] using hxQ)
    · apply Finset.disjoint_left.mp hQcycle hxQ
      rw [hbaseSupport] at hxBase
      exact Finset.mem_of_mem_erase hxBase
  have hkvBase : kv ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKv.symm, hkvCycle⟩
  have hqCross : ∃! e : α × α,
      e.1 ∈ Q ∧ e.2 ∈ P ∪ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    refine ⟨(q.penultimate, kv),
      ⟨by simp [Q, hqPen], Finset.mem_union_right P hkvBase, hqAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxQ, hyUnion, hxy⟩
    rcases Finset.mem_union.mp hyUnion with hyP | hyBase
    · exact (hnoAdjPQ (by simpa [P] using hyP) (by simpa [Q] using hxQ)
        hxy.symm).elim
    · have hyCycle : y ∈ c.support.toFinset := by
        rw [hbaseSupport] at hyBase
        exact Finset.mem_of_mem_erase hyBase
      rcases hqUnique (by simpa [Q] using hxQ) hyCycle hxy with ⟨rfl, rfl⟩
      rfl
  have hUnionTree :
      (G.induce ((Q ∪ (P ∪ base.support.toFinset) : Finset α) : Set α)).IsTree :=
    hQTree.induce_union_of_disjoint_of_unique_adj_splice
      hUnionP hQUnion hqCross
  have hPbaseCard :
      (P ∪ base.support.toFinset).card =
        P.card + base.support.toFinset.card :=
    Finset.card_union_of_disjoint hPbase
  have hUnionCard :
      (Q ∪ (P ∪ base.support.toFinset)).card =
        Q.card + (P ∪ base.support.toFinset).card :=
    Finset.card_union_of_disjoint hQUnion
  have hsize :
      G.girth - 1 + p.length + q.length ≤
        (Q ∪ (P ∪ base.support.toFinset)).card := by
    rw [hUnionCard, hPbaseCard, show P.card = p.length by simpa [P] using hPcard,
      show Q.card = q.length by simpa [Q] using hQcard, hbaseCard, hcLength]
    omega
  exact hsize.trans hUnionTree.card_le_largestInducedTreeSize_splice
/-- Three-tail noninteracting package used by L8: three pairwise disjoint and
nonadjacent nearest-cycle descents, together with a safe retained cycle path, form one
induced tree of the exact required order. -/
lemma Walk.three_noninteracting_descents_largestInducedTreeSize
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length) (htPos : 0 < t.length)
    (hdisjPQ : Disjoint p.dropLast.support.toFinset q.dropLast.support.toFinset)
    (hdisjPT : Disjoint p.dropLast.support.toFinset t.dropLast.support.toFinset)
    (hdisjQT : Disjoint q.dropLast.support.toFinset t.dropLast.support.toFinset)
    (hnoAdjPQ : ∀ ⦃x y : α⦄, x ∈ p.dropLast.support.toFinset →
      y ∈ q.dropLast.support.toFinset → ¬G.Adj x y)
    (hnoAdjPT : ∀ ⦃x y : α⦄, x ∈ p.dropLast.support.toFinset →
      y ∈ t.dropLast.support.toFinset → ¬G.Adj x y)
    (hnoAdjQT : ∀ ⦃x y : α⦄, x ∈ q.dropLast.support.toFinset →
      y ∈ t.dropLast.support.toFinset → ¬G.Adj x y) :
    G.girth - 1 + p.length + q.length + t.length ≤ largestInducedTreeSize G := by
  let P := p.dropLast.support.toFinset
  let Q := q.dropLast.support.toFinset
  let R := t.dropLast.support.toFinset
  obtain ⟨eraseRoot, hrMem, hrNeKu, hrNeKv, hrNeKw⟩ :=
    hc.exists_support_ne_three_splice hcLength hg
  obtain ⟨hPTree, hPcard⟩ := p.nearest_descent_dropLast_tree_and_card
    (by simpa using hku) hp hpPos
  obtain ⟨hQTree, hQcard⟩ := q.nearest_descent_dropLast_tree_and_card
    (by simpa using hkv) hq hqPos
  obtain ⟨hRTree, hRcard⟩ := t.nearest_descent_dropLast_tree_and_card
    (by simpa using hkw) ht htPos
  obtain ⟨hpPen, hkuCycle, hpAdj, hpUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      p hku hp hpPos
  obtain ⟨hqPen, hkvCycle, hqAdj, hqUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      q hkv hq hqPos
  obtain ⟨htPen, hkwCycle, htAdj, htUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment hc hcLength hg hconn
      t hkw ht htPos
  let rot := c.rotate hrMem
  let base := rot.tail.dropLast
  have hbaseCert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase eraseRoot ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [rot, base] using
      hc.erase_vertex_path_certificate_splice hrMem hcLength
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, hbaseCard⟩
  have hPcycle : Disjoint P c.support.toFinset := by
    dsimp [P]
    exact p.nearest_descent_dropLast_disjoint_finset_target hp hpPos
  have hQcycle : Disjoint Q c.support.toFinset := by
    dsimp [Q]
    exact q.nearest_descent_dropLast_disjoint_finset_target hq hqPos
  have hRcycle : Disjoint R c.support.toFinset := by
    dsimp [R]
    exact t.nearest_descent_dropLast_disjoint_finset_target ht htPos
  have hPbase : Disjoint P base.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxP hxBase
    apply Finset.disjoint_left.mp hPcycle hxP
    rw [hbaseSupport] at hxBase
    exact Finset.mem_of_mem_erase hxBase
  have hkuBase : ku ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKu.symm, hkuCycle⟩
  have hpCross : ∃! e : α × α,
      e.1 ∈ P ∧ e.2 ∈ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    refine ⟨(p.penultimate, ku), ⟨by simp [P, hpPen], hkuBase, hpAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxP, hyBase, hxy⟩
    have hyCycle : y ∈ c.support.toFinset := by
      rw [hbaseSupport] at hyBase
      exact Finset.mem_of_mem_erase hyBase
    rcases hpUnique (by simpa [P] using hxP) hyCycle hxy with ⟨rfl, rfl⟩
    rfl
  have hUnionP :
      (G.induce ((P ∪ base.support.toFinset : Finset α) : Set α)).IsTree :=
    hPTree.induce_union_of_disjoint_of_unique_adj_splice
      hbaseTree hPbase hpCross
  have hQUnion : Disjoint Q (P ∪ base.support.toFinset) := by
    rw [Finset.disjoint_left]
    intro x hxQ hxUnion
    rcases Finset.mem_union.mp hxUnion with hxP | hxBase
    · exact Finset.disjoint_left.mp hdisjPQ (by simpa [P] using hxP)
        (by simpa [Q] using hxQ)
    · apply Finset.disjoint_left.mp hQcycle hxQ
      rw [hbaseSupport] at hxBase
      exact Finset.mem_of_mem_erase hxBase
  have hkvBase : kv ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKv.symm, hkvCycle⟩
  have hqCross : ∃! e : α × α,
      e.1 ∈ Q ∧ e.2 ∈ P ∪ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    refine ⟨(q.penultimate, kv),
      ⟨by simp [Q, hqPen], Finset.mem_union_right P hkvBase, hqAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxQ, hyUnion, hxy⟩
    rcases Finset.mem_union.mp hyUnion with hyP | hyBase
    · exact (hnoAdjPQ (by simpa [P] using hyP) (by simpa [Q] using hxQ)
        hxy.symm).elim
    · have hyCycle : y ∈ c.support.toFinset := by
        rw [hbaseSupport] at hyBase
        exact Finset.mem_of_mem_erase hyBase
      rcases hqUnique (by simpa [Q] using hxQ) hyCycle hxy with ⟨rfl, rfl⟩
      rfl
  have hUnionPQ :
      (G.induce ((Q ∪ (P ∪ base.support.toFinset) : Finset α) : Set α)).IsTree :=
    hQTree.induce_union_of_disjoint_of_unique_adj_splice
      hUnionP hQUnion hqCross
  have hRUnion : Disjoint R (Q ∪ (P ∪ base.support.toFinset)) := by
    rw [Finset.disjoint_left]
    intro x hxR hxUnion
    rcases Finset.mem_union.mp hxUnion with hxQ | hxRest
    · exact Finset.disjoint_left.mp hdisjQT (by simpa [Q] using hxQ)
        (by simpa [R] using hxR)
    · rcases Finset.mem_union.mp hxRest with hxP | hxBase
      · exact Finset.disjoint_left.mp hdisjPT (by simpa [P] using hxP)
          (by simpa [R] using hxR)
      · apply Finset.disjoint_left.mp hRcycle hxR
        rw [hbaseSupport] at hxBase
        exact Finset.mem_of_mem_erase hxBase
  have hkwBase : kw ∈ base.support.toFinset := by
    rw [hbaseSupport]
    exact Finset.mem_erase.mpr ⟨hrNeKw.symm, hkwCycle⟩
  have htCross : ∃! e : α × α,
      e.1 ∈ R ∧ e.2 ∈ Q ∪ (P ∪ base.support.toFinset) ∧ G.Adj e.1 e.2 := by
    refine ⟨(t.penultimate, kw),
      ⟨by simp [R, htPen],
        Finset.mem_union_right Q (Finset.mem_union_right P hkwBase), htAdj⟩, ?_⟩
    rintro ⟨x, y⟩ ⟨hxR, hyUnion, hxy⟩
    rcases Finset.mem_union.mp hyUnion with hyQ | hyRest
    · exact (hnoAdjQT (by simpa [Q] using hyQ) (by simpa [R] using hxR)
        hxy.symm).elim
    · rcases Finset.mem_union.mp hyRest with hyP | hyBase
      · exact (hnoAdjPT (by simpa [P] using hyP) (by simpa [R] using hxR)
          hxy.symm).elim
      · have hyCycle : y ∈ c.support.toFinset := by
          rw [hbaseSupport] at hyBase
          exact Finset.mem_of_mem_erase hyBase
        rcases htUnique (by simpa [R] using hxR) hyCycle hxy with ⟨rfl, rfl⟩
        rfl
  have hUnionTree :
      (G.induce ((R ∪ (Q ∪ (P ∪ base.support.toFinset)) : Finset α) :
        Set α)).IsTree :=
    hRTree.induce_union_of_disjoint_of_unique_adj_splice
      hUnionPQ hRUnion htCross
  have hPbaseCard :
      (P ∪ base.support.toFinset).card =
        P.card + base.support.toFinset.card :=
    Finset.card_union_of_disjoint hPbase
  have hPQbaseCard :
      (Q ∪ (P ∪ base.support.toFinset)).card =
        Q.card + (P ∪ base.support.toFinset).card :=
    Finset.card_union_of_disjoint hQUnion
  have hUnionCard :
      (R ∪ (Q ∪ (P ∪ base.support.toFinset))).card =
        R.card + (Q ∪ (P ∪ base.support.toFinset)).card :=
    Finset.card_union_of_disjoint hRUnion
  have hsize :
      G.girth - 1 + p.length + q.length + t.length ≤
        (R ∪ (Q ∪ (P ∪ base.support.toFinset))).card := by
    rw [hUnionCard, hPQbaseCard, hPbaseCard,
      show P.card = p.length by simpa [P] using hPcard,
      show Q.card = q.length by simpa [Q] using hQcard,
      show R.card = t.length by simpa [R] using hRcard,
      hbaseCard, hcLength]
    omega
  exact hsize.trans hUnionTree.card_le_largestInducedTreeSize_splice
/-- The interacting splice already yields the full induced-tree lower bound obtained by
adjoining its certified outside tree to the girth cycle with one vertex erased. -/
lemma Walk.interacting_descents_splice_L7b_largestInducedTreeSize
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (hku : ku ∈ c.support)
    (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (hex : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)) :
    G.girth + G.dist u v ≤ largestInducedTreeSize G := by
  obtain ⟨F, eraseRoot, hrMem, _, hFDisj, hFTree, hcross, hFcard⟩ :=
    Walk.interacting_descents_splice_L7b_outside_cycle hc hcLength hg hconn
      p q hku hkv hp hq hpPos hqPos hex
  let r := c.rotate hrMem
  let base := r.tail.dropLast
  have hbaseCert :
      base.IsPath ∧
        base.support.toFinset = c.support.toFinset.erase eraseRoot ∧
        (G.induce (base.support.toFinset : Set α)).IsTree ∧
        base.support.toFinset.card = c.length - 1 := by
    simpa only [r, base] using
      hc.erase_vertex_path_certificate_splice hrMem hcLength
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, hbaseCard⟩
  have hdisjBase : Disjoint F base.support.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxF hxBase
    apply Finset.disjoint_left.mp hFDisj hxF
    rw [hbaseSupport] at hxBase
    exact Finset.mem_of_mem_erase hxBase
  have hcrossBase : ∃! e : α × α,
      e.1 ∈ F ∧ e.2 ∈ base.support.toFinset ∧ G.Adj e.1 e.2 := by
    rw [hbaseSupport]
    exact hcross
  have hUnionTree :
      (G.induce ((F ∪ base.support.toFinset : Finset α) : Set α)).IsTree :=
    hFTree.induce_union_of_disjoint_of_unique_adj_splice
      hbaseTree hdisjBase hcrossBase
  have hUnionCard :
      (F ∪ base.support.toFinset).card =
        F.card + base.support.toFinset.card :=
    Finset.card_union_of_disjoint hdisjBase
  have hsize :
      G.girth + G.dist u v ≤ (F ∪ base.support.toFinset).card := by
    rw [hUnionCard, hbaseCard, hcLength]
    omega
  exact hsize.trans hUnionTree.card_le_largestInducedTreeSize_splice
/-- Positive-three-tail structural core of L8.  An interacting pair uses L7(b);
otherwise the three outside paths and retained cycle use the noninteracting package. -/
lemma Walk.three_positive_descents_L8_dichotomy
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length) (htPos : 0 < t.length)
    {f : ℕ} (hfuv : f ≤ G.dist u v) (hfuw : f ≤ G.dist u w)
    (hfvw : f ≤ G.dist v w) :
    min (G.girth + f) (G.girth - 1 + p.length + q.length + t.length) ≤
      largestInducedTreeSize G := by
  by_cases hexPQ : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)
  · have hbound := Walk.interacting_descents_splice_L7b_largestInducedTreeSize
      hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos hexPQ
    omega
  by_cases hexPT : ∃ i : ℕ, i < t.length ∧
      InteractsFinset G p.dropLast.support.toFinset (t.getVert i)
  · have hbound := Walk.interacting_descents_splice_L7b_largestInducedTreeSize
      hc hcLength hg hconn p t hku hkw hp ht hpPos htPos hexPT
    omega
  by_cases hexQT : ∃ i : ℕ, i < t.length ∧
      InteractsFinset G q.dropLast.support.toFinset (t.getVert i)
  · have hbound := Walk.interacting_descents_splice_L7b_largestInducedTreeSize
      hc hcLength hg hconn q t hkv hkw hq ht hqPos htPos hexQT
    omega
  obtain ⟨hdisjPQ, hnoAdjPQ⟩ :=
    q.dropLast_disjoint_and_nonadjacent_of_no_interaction_index
      p.dropLast.support.toFinset hqPos hexPQ
  obtain ⟨hdisjPT, hnoAdjPT⟩ :=
    t.dropLast_disjoint_and_nonadjacent_of_no_interaction_index
      p.dropLast.support.toFinset htPos hexPT
  obtain ⟨hdisjQT, hnoAdjQT⟩ :=
    t.dropLast_disjoint_and_nonadjacent_of_no_interaction_index
      q.dropLast.support.toFinset htPos hexQT
  have hbound := Walk.three_noninteracting_descents_largestInducedTreeSize
    hc hcLength hg hconn p q t hku hkv hkw hp hq ht hpPos hqPos htPos
      hdisjPQ hdisjPT hdisjQT hnoAdjPQ hnoAdjPT hnoAdjQT
  omega
/-- Arithmetic closure of L8 when all three descents are positive. -/
lemma Walk.three_positive_descents_main_range_bound
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length) (htPos : 0 < t.length)
    {f : ℕ} (hfuv : f ≤ G.dist u v) (hfuw : f ≤ G.dist u w)
    (hfvw : f + 1 ≤ G.dist v w) :
    f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G := by
  have hL8 := Walk.three_positive_descents_L8_dichotomy
    hc hcLength hg hconn p q t hku hkv hkw hp hq ht hpPos hqPos htPos
      hfuv hfuw (by omega : f ≤ G.dist v w)
  have hL6 := hc.three_arc_inequality_splice hconn p q t hku hkv hkw
  have hmetric :
      3 * f + 1 ≤ 2 * (p.length + q.length + t.length) + G.girth := by
    rw [← hcLength]
    omega
  have hleft : f + (G.girth - G.girth / 3) ≤ G.girth + f := by omega
  have hright : f + (G.girth - G.girth / 3) ≤
      G.girth - 1 + p.length + q.length + t.length := by
    omega
  exact (Nat.le_min.mpr ⟨hleft, hright⟩).trans hL8
/-- Two-positive-tail structural dichotomy: interact and splice, or retain both
noninteracting outside paths. -/
lemma Walk.two_positive_descents_L8_dichotomy
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    {f : ℕ} (hfuv : f ≤ G.dist u v) :
    min (G.girth + f) (G.girth - 1 + p.length + q.length) ≤
      largestInducedTreeSize G := by
  by_cases hex : ∃ i : ℕ, i < q.length ∧
      InteractsFinset G p.dropLast.support.toFinset (q.getVert i)
  · have hbound := Walk.interacting_descents_splice_L7b_largestInducedTreeSize
      hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos hex
    omega
  · obtain ⟨hdisj, hnoAdj⟩ :=
      q.dropLast_disjoint_and_nonadjacent_of_no_interaction_index
        p.dropLast.support.toFinset hqPos hex
    have hbound := Walk.noninteracting_descents_L7a_largestInducedTreeSize
      hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos hdisj hnoAdj
    omega

/-- Arithmetic closure when exactly two of the three selected descents are positive. -/
lemma Walk.two_positive_descents_bound
    {z u ku v kv w : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hw : w ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    {f : ℕ} (hfuv : f ≤ G.dist u v)
    (hlower : 3 * f + 1 ≤ G.dist u v + G.dist u w + G.dist v w) :
    f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G := by
  have hL8 := Walk.two_positive_descents_L8_dichotomy
    hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos hfuv
  have hL6 := hc.three_arc_inequality_splice hconn p q
    (Walk.nil : G.Walk w w) hku hkv hw
  have hmetric : 3 * f + 1 ≤ 2 * (p.length + q.length) + G.girth := by
    rw [← hcLength]
    simpa using hlower.trans hL6
  have hleft : f + (G.girth - G.girth / 3) ≤ G.girth + f := by omega
  have hright : f + (G.girth - G.girth / 3) ≤
      G.girth - 1 + p.length + q.length := by
    omega
  exact (Nat.le_min.mpr ⟨hleft, hright⟩).trans hL8

/-- Arithmetic closure when exactly one selected descent is positive. -/
lemma Walk.one_positive_descent_main_range_bound
    {z u ku v w : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (hku : ku ∈ c.support)
    (hv : v ∈ c.support) (hw : w ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) {f : ℕ}
    (hlower : 3 * f + 1 ≤ G.dist u v + G.dist u w + G.dist v w)
    (hmain : G.girth - 2 * (G.girth / 3) ≤ f) :
    f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G := by
  have htree := Walk.one_descent_largestInducedTreeSize
    hc hcLength hg hconn p hku hp hpPos
  have hL6 := hc.three_arc_inequality_splice hconn p
    (Walk.nil : G.Walk v v) (Walk.nil : G.Walk w w) hku hv hw
  have hmetric : 3 * f + 1 ≤ 2 * p.length + G.girth := by
    rw [← hcLength]
    simpa using hlower.trans hL6
  have htarget : f + (G.girth - G.girth / 3) ≤
      G.girth - 1 + p.length := by
    omega
  exact htarget.trans htree

omit [Fintype α] [DecidableEq α] in
/-- In the main range the three selected terminals cannot all lie on the cycle. -/
lemma Walk.IsCycle.not_three_cycle_vertices_main_range
    {z u v w : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hu : u ∈ c.support)
    (hv : v ∈ c.support) (hw : w ∈ c.support) {f : ℕ}
    (hlower : 3 * f + 1 ≤ G.dist u v + G.dist u w + G.dist v w)
    (hmain : G.girth - 2 * (G.girth / 3) ≤ f) : False := by
  have hroot := hc.sum_three_dist_le_length_splice hu hv hw
  rw [hcLength] at hroot
  omega
/-- L8 arithmetic closure for three nearest-cycle descents, allowing any of
its three descents to have length zero. -/
lemma Walk.three_descents_main_range_bound
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    {f : ℕ} (hfuv : f ≤ G.dist u v) (hfuw : f ≤ G.dist u w)
    (hfvw : f + 1 ≤ G.dist v w)
    (hmain : G.girth - 2 * (G.girth / 3) ≤ f) :
    f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G := by
  have hlower :
      3 * f + 1 ≤ G.dist u v + G.dist u w + G.dist v w := by omega
  by_cases hpPos : 0 < p.length
  · by_cases hqPos : 0 < q.length
    · by_cases htPos : 0 < t.length
      · exact Walk.three_positive_descents_main_range_bound
          hc hcLength hg hconn p q t hku hkv hkw hp hq ht hpPos hqPos htPos
            hfuv hfuw hfvw
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact Walk.two_positive_descents_bound
          hc hcLength hg hconn p q hku hkv hwCycle hp hq hpPos hqPos hfuv hlower
    · have hqZero : q.length = 0 := Nat.eq_zero_of_not_pos hqPos
      have hvEq : v = kv := q.eq_of_length_eq_zero hqZero
      have hvCycle : v ∈ c.support := by simpa [hvEq] using hkv
      by_cases htPos : 0 < t.length
      · exact Walk.two_positive_descents_bound
          hc hcLength hg hconn p t hku hkw hvCycle hp ht hpPos htPos hfuw
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact Walk.one_positive_descent_main_range_bound
          hc hcLength hg hconn p hku hvCycle hwCycle hp hpPos hlower hmain
  · have hpZero : p.length = 0 := Nat.eq_zero_of_not_pos hpPos
    have huEq : u = ku := p.eq_of_length_eq_zero hpZero
    have huCycle : u ∈ c.support := by simpa [huEq] using hku
    by_cases hqPos : 0 < q.length
    · by_cases htPos : 0 < t.length
      · exact Walk.two_positive_descents_bound
          hc hcLength hg hconn q t hkv hkw huCycle hq ht hqPos htPos
            (by omega : f ≤ G.dist v w)
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact Walk.one_positive_descent_main_range_bound
          hc hcLength hg hconn q hkv huCycle hwCycle hq hqPos
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
            hmain
    · have hqZero : q.length = 0 := Nat.eq_zero_of_not_pos hqPos
      have hvEq : v = kv := q.eq_of_length_eq_zero hqZero
      have hvCycle : v ∈ c.support := by simpa [hvEq] using hkv
      by_cases htPos : 0 < t.length
      · exact Walk.one_positive_descent_main_range_bound
          hc hcLength hg hconn t hkw huCycle hvCycle ht htPos
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
            hmain
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact (hc.not_three_cycle_vertices_main_range hcLength huCycle hvCycle
          hwCycle hlower hmain).elim
omit [DecidableEq α] in
/-- The maximum distance to a set is attained on a nonempty finite vertex type. -/
lemma exists_eccSet_witness_splice [Nonempty α] (S : Set α) :
    ∃ v, G.distToSet v S = G.eccSet S := by
  simp only [eccSet]
  split_ifs with hne
  · obtain ⟨w, -, hval⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    exact ⟨w, hval⟩
  · exact absurd (Finset.univ_nonempty.image _) hne

omit [DecidableEq α] in
/-- The periphery of a finite nonempty graph is nonempty. -/
lemma maxEccentricityVertices_nonempty_splice [Nonempty α] :
    (maxEccentricityVertices G).Nonempty := by
  obtain ⟨b, hb⟩ := exists_eccent_eq_ediam_of_finite (G := G)
  exact ⟨b, hb⟩

omit [DecidableEq α] in
/-- Both ends of a diametral pair are peripheral in a finite connected graph. -/
lemma diametral_endpoints_mem_maxEccentricityVertices_splice [Nonempty α]
    (hconn : G.Connected) {b w : α} (hbw : G.dist b w = G.diam) :
    b ∈ maxEccentricityVertices G ∧ w ∈ maxEccentricityVertices G := by
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hed : G.edist b w = G.ediam := by
    rw [← (hconn.preconnected b w).coe_dist_eq_edist, hbw, diam]
    exact ENat.coe_toNat hfinite
  constructor
  · change G.eccent b = G.ediam
    exact le_antisymm eccent_le_ediam (by
      calc
        G.ediam = G.edist b w := hed.symm
        _ ≤ G.eccent b := edist_le_eccent)
  · change G.eccent w = G.ediam
    exact le_antisymm eccent_le_ediam (by
      calc
        G.ediam = G.edist b w := hed.symm
        _ = G.edist w b := edist_comm
        _ ≤ G.eccent w := edist_le_eccent)

omit [DecidableEq α] in
/-- T4: positive eccentricity of the periphery is strictly below the diameter. -/
lemma eccSet_maxEccentricityVertices_add_one_le_diam_splice [Nontrivial α]
    (hconn : G.Connected)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G)) :
    G.eccSet (maxEccentricityVertices G) + 1 ≤ G.diam := by
  let B : Set α := maxEccentricityVertices G
  let f := G.eccSet B
  change f + 1 ≤ G.diam
  have hfpos' : 0 < f := by
    dsimp [f, B]
    exact hfpos
  obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
  obtain ⟨b, hb⟩ := maxEccentricityVertices_nonempty_splice (G := G)
  have hbB : b ∈ B := hb
  have hxNot : x ∉ B := by
    intro hxB
    have hle : G.distToSet x B ≤ 0 := by
      simpa using distToSet_le_dist_of_mem_public (G := G) x hxB
    have hzero : G.eccSet B = 0 := by
      rw [← hx]
      exact Nat.eq_zero_of_le_zero hle
    have hfzero : f = 0 := hzero
    exact (Nat.ne_of_gt hfpos') hfzero
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hsetLe : f ≤ G.dist x b := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x b := distToSet_le_dist_of_mem_public (G := G) x hbB
  have hdistLe : G.dist x b ≤ G.diam := dist_le_diam hfinite
  have hfLe : f ≤ G.diam := hsetLe.trans hdistLe
  by_contra hstrict
  have hdiamLe : G.diam ≤ f := by omega
  have hfd : f = G.diam := Nat.le_antisymm hfLe hdiamLe
  have hxb : G.dist x b = G.diam := by omega
  have hed : G.edist x b = G.ediam := by
    rw [← (hconn.preconnected x b).coe_dist_eq_edist, hxb, diam]
    exact ENat.coe_toNat hfinite
  apply hxNot
  change G.eccent x = G.ediam
  exact le_antisymm eccent_le_ediam (by
    calc
      G.ediam = G.edist x b := hed.symm
      _ ≤ G.eccent x := edist_le_eccent)

omit [DecidableEq α] in
/-- A connected graph has a geodesic from any vertex to a nearest member of a
nonempty target set. -/
lemma Connected.exists_path_length_eq_distToSet_splice (hconn : G.Connected)
    (u : α) {S : Set α} (hS : S.Nonempty) :
    ∃ s ∈ S, ∃ p : G.Walk u s,
      p.IsPath ∧ p.length = G.distToSet u S := by
  obtain ⟨s, hs, hdist⟩ := exists_mem_dist_eq_distToSet (G := G) u hS
  obtain ⟨p, hpPath, hpLength⟩ := hconn.exists_path_of_dist u s
  exact ⟨s, hs, p, hpPath, hpLength.trans hdist.symm⟩

/-- C8 after extracting an eccentricity realizer, a diametral pair, a shortest
cycle, and their three nearest-cycle descents. -/
lemma cyclic_main_range_bound_splice [Nontrivial α]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : 5 ≤ G.girth)
    (hmain : G.girth - 2 * (G.girth / 3) ≤
      G.eccSet (maxEccentricityVertices G)) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  let B : Set α := maxEccentricityVertices G
  let f := G.eccSet B
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  have hcycleSet : ((c.support.toFinset : Finset α) : Set α).Nonempty := by
    exact ⟨z, by simp⟩
  obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  obtain ⟨hbB, hwB⟩ :=
    diametral_endpoints_mem_maxEccentricityVertices_splice hconn hbw
  have hfxb : f ≤ G.dist x b := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x b := distToSet_le_dist_of_mem_public (G := G) x hbB
  have hfxw : f ≤ G.dist x w := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x w := distToSet_le_dist_of_mem_public (G := G) x hwB
  have hfD : f + 1 ≤ G.diam := by
    simpa only [B, f] using
      eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  have hfbw : f + 1 ≤ G.dist b w := by simpa only [hbw] using hfD
  obtain ⟨kx, hkx, p, _, hp⟩ :=
    hconn.exists_path_length_eq_distToSet_splice x hcycleSet
  obtain ⟨kb, hkb, q, _, hq⟩ :=
    hconn.exists_path_length_eq_distToSet_splice b hcycleSet
  obtain ⟨kw, hkw, t, _, ht⟩ :=
    hconn.exists_path_length_eq_distToSet_splice w hcycleSet
  have hkx' : kx ∈ c.support := by simpa using hkx
  have hkb' : kb ∈ c.support := by simpa using hkb
  have hkw' : kw ∈ c.support := by simpa using hkw
  exact Walk.three_descents_main_range_bound
    hc hcLength hg hconn p q t hkx' hkb' hkw' hp hq ht hfxb hfxw hfbw
      (by simpa only [B, f] using hmain)
/-- Every geodesic is an induced path tree, giving the universal distance
lower bound for the largest induced tree. -/
lemma dist_add_one_le_largestInducedTreeSize_splice (hconn : G.Connected)
    (u v : α) : G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hpPath, hpLength⟩ := hconn.exists_path_of_dist u v
  have htree := p.induce_support_isTree_of_length_eq_dist hpLength
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hbound := htree.card_le_largestInducedTreeSize_splice
  omega

/-- The diameter plus one is a lower bound for the largest induced tree. -/
lemma diam_add_one_le_largestInducedTreeSize_splice [Nonempty α]
    (hconn : G.Connected) : G.diam + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  rw [← huv]
  exact dist_add_one_le_largestInducedTreeSize_splice hconn u v

/-- The girth-three hard branch follows from T4 and a diametral geodesic. -/
lemma cyclic_girth_three_bound_splice [Nontrivial α]
    (hconn : G.Connected)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : G.girth = 3) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  have hfD :=
    eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  have htree := diam_add_one_le_largestInducedTreeSize_splice hconn
  omega

/-- Below the L8 main range, the shortest cycle with one vertex erased already
has enough vertices. -/
lemma cyclic_small_f_bound_splice
    (hcyc : ¬G.IsAcyclic)
    {f : ℕ} (hf : f ≤ G.girth / 3 - 1) :
    f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G := by
  have hg3 : 3 ≤ G.girth := three_le_girth hcyc
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  have htree := hc.girth_sub_one_le_largestInducedTreeSize_splice hcLength
  omega
omit [Fintype α] [DecidableEq α] in
/-- A four-cycle has an edge avoiding any prescribed vertex. -/
lemma Walk.IsCycle.exists_adjacent_avoiding_of_length_eq_four_splice
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle) (hcFour : c.length = 4) :
    ∃ u v, u ≠ x ∧ v ≠ x ∧ G.Adj u v := by
  have hget : ∀ {i j : ℕ}, i ≤ 3 → j ≤ 3 → i ≠ j →
      c.getVert i ≠ c.getVert j := by
    intro i j hi hj hij heq
    apply hij
    apply hc.getVert_injOn'
    · simp only [Set.mem_setOf_eq, hcFour]
      omega
    · simp only [Set.mem_setOf_eq, hcFour]
      omega
    · exact heq
  by_cases hx0 : x = c.getVert 0
  · refine ⟨c.getVert 1, c.getVert 2, ?_, ?_, c.adj_getVert_succ (by omega)⟩
    · intro h
      exact hget (i := 1) (j := 0) (by omega) (by omega) (by omega) (h.trans hx0)
    · intro h
      exact hget (i := 2) (j := 0) (by omega) (by omega) (by omega) (h.trans hx0)
  · by_cases hx1 : x = c.getVert 1
    · refine ⟨c.getVert 2, c.getVert 3, ?_, ?_, c.adj_getVert_succ (by omega)⟩
      · intro h
        exact hget (i := 2) (j := 1) (by omega) (by omega) (by omega) (h.trans hx1)
      · intro h
        exact hget (i := 3) (j := 1) (by omega) (by omega) (by omega) (h.trans hx1)
    · exact ⟨c.getVert 0, c.getVert 1, Ne.symm hx0, Ne.symm hx1,
        c.adj_getVert_succ (by omega)⟩

/-- T6 in the only form needed by L9: a positive periphery-distance term and
girth four force diameter at least three. -/
lemma three_le_diam_of_girth_four_eccSet_pos_splice [Nontrivial α]
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : G.girth = 4) : 3 ≤ G.diam := by
  by_contra hD
  have hfD :=
    eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  have hdiam : G.diam = 2 := by omega
  let B : Set α := maxEccentricityVertices G
  obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
  have hxNot : x ∉ B := by
    intro hxB
    have hle : G.distToSet x B ≤ 0 := by
      simpa using distToSet_le_dist_of_mem_public (G := G) x hxB
    have hzero : G.eccSet B = 0 := by
      rw [← hx]
      exact Nat.eq_zero_of_le_zero hle
    have : G.eccSet (maxEccentricityVertices G) = 0 := by exact hzero
    omega
  have heccLe : computable_eccent G x ≤ computable_ediam G := by
    have hle : G.eccent x ≤ G.ediam := eccent_le_ediam
    rw [eccent_eq_computable G hconn x, ediam_eq_computable G hconn] at hle
    exact_mod_cast hle
  have heccNe : computable_eccent G x ≠ computable_ediam G := by
    intro heq
    apply hxNot
    change G.eccent x = G.ediam
    rw [eccent_eq_computable G hconn x, ediam_eq_computable G hconn, heq]
  have hcompDiam : computable_ediam G = G.diam := by
    have hco := congrArg ENat.toNat (ediam_eq_computable G hconn)
    simpa [diam] using hco.symm
  have heccOne : computable_eccent G x ≤ 1 := by omega
  have hxUniversal : ∀ y : α, y ≠ x → G.Adj x y := by
    intro y hyx
    have hxy : G.dist x y ≤ computable_eccent G x := by
      have hle : G.edist x y ≤ G.eccent x := edist_le_eccent
      rw [← (hconn.preconnected x y).coe_dist_eq_edist,
        eccent_eq_computable G hconn x] at hle
      exact_mod_cast hle
    have hpos : 0 < G.dist x y := hconn.pos_dist_of_ne hyx.symm
    have hone : G.dist x y = 1 := by omega
    exact dist_eq_one_iff_adj.mp hone
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr (by
    intro hacyc
    have := hacyc.girth_eq_zero
    omega)
  have hcFour : c.length = 4 := by omega
  obtain ⟨u, v, hux, hvx, huv⟩ :=
    hc.exists_adjacent_avoiding_of_length_eq_four_splice hcFour (x := x)
  let e : G.Walk u v := Walk.cons huv Walk.nil
  have hePath : e.IsPath := by
    dsimp [e]
    simp [huv.ne]
  have hxOut : x ∉ e.support := by
    intro hxmem
    have hxmem' : x = u ∨ x = v := by simpa [e] using hxmem
    exact hxmem'.elim (fun h => hux h.symm) (fun h => hvx h.symm)
  have htri : ((e.concat (hxUniversal v hvx).symm).concat
      (hxUniversal u hux)).IsCycle :=
    hePath.concat_two_isCycle_splice huv.ne hxOut
      (hxUniversal v hvx).symm (hxUniversal u hux)
  have hbound := G.girth_le_length htri
  simp only [Walk.length_concat, e, Walk.length_cons, Walk.length_nil] at hbound
  omega
/-- A vertex with a unique attachment to a geodesic enlarges its induced path
tree by one vertex. -/
lemma Walk.geodesic_unique_attachment_tree_bound_splice
    {b w y a : α} (p : G.Walk b w) (hp : p.length = G.dist b w)
    (hy : y ∉ p.support) (ha : a ∈ p.support) (hya : G.Adj y a)
    (huniq : ∀ ⦃z : α⦄, z ∈ p.support → G.Adj y z → z = a) :
    p.length + 2 ≤ largestInducedTreeSize G := by
  have hbase := p.induce_support_isTree_of_length_eq_dist hp
  have hyFin : y ∉ p.support.toFinset := by simpa using hy
  have haFin : a ∈ p.support.toFinset := by simpa using ha
  have htree := hbase.induce_insert_of_unique_adj hyFin haFin hya (by
    intro z hz hAdj
    exact huniq (by simpa using hz) hAdj)
  have hpPath := p.isPath_of_length_eq_dist hp
  have hcard : (insert y p.support.toFinset).card = p.length + 2 := by
    rw [Finset.card_insert_of_notMem hyFin,
      List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hbound := htree.card_le_largestInducedTreeSize_splice
  omega

/-- Replacing a two-edge geodesic segment by the opposite side of a four-cycle
preserves geodesicity; a second-depth vertex then attaches uniquely. -/
lemma Walk.geodesic_two_step_reroute_tree_bound_splice
    {b w y x₂ : α} (p : G.Walk b w) (hp : p.length = G.dist b w)
    {i : ℕ} (hi : i + 2 ≤ p.length)
    (hy : y ∉ p.support) (hiy : G.Adj (p.getVert i) y)
    (hyi₂ : G.Adj y (p.getVert (i + 2)))
    (hx₂ : x₂ ∉ p.support) (hx₂y : G.Adj x₂ y)
    (hx₂No : ∀ ⦃z : α⦄, z ∈ p.support → ¬G.Adj x₂ z) :
    p.length + 2 ≤ largestInducedTreeSize G := by
  let r₀ := ((p.take i).concat hiy).concat hyi₂
  let r : G.Walk b w := r₀.append (p.drop (i + 2))
  have hrLen : r.length = p.length := by
    dsimp [r, r₀]
    rw [Walk.length_append, Walk.length_concat, Walk.length_concat,
      Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
    omega
  have hrGeod : r.length = G.dist b w := hrLen.trans hp
  have hrTree := r.induce_support_isTree_of_length_eq_dist hrGeod
  have hrSubset : ∀ ⦃z : α⦄, z ∈ r.support → z = y ∨ z ∈ p.support := by
    intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · dsimp [r₀] at hz
      have hz' : (z ∈ (p.take i).support ∨ z = y) ∨ z = p.getVert (i + 2) := by
        simpa only [Walk.support_concat, List.concat_eq_append, List.mem_append,
          List.mem_singleton] using hz
      rcases hz' with (hz | rfl) | rfl
      · exact Or.inr ((Walk.isSubwalk_take p i).support_subset hz)
      · exact Or.inl rfl
      · exact Or.inr (p.getVert_mem_support (i + 2))
    · exact Or.inr ((Walk.isSubwalk_drop p (i + 2)).support_subset hz)
  have hx₂NotR : x₂ ∉ r.support.toFinset := by
    intro hxmem
    rcases hrSubset (by simpa using hxmem) with hxy | hxp
    · exact hx₂y.ne hxy
    · exact hx₂ hxp
  have hyR : y ∈ r.support.toFinset := by
    have : y ∈ r₀.support := by simp [r₀]
    exact by
      simpa only [List.mem_toFinset, r, Walk.mem_support_append_iff] using Or.inl this
  have huniq : ∀ ⦃z : α⦄, z ∈ r.support.toFinset → G.Adj x₂ z → z = y := by
    intro z hz hAdj
    rcases hrSubset (by simpa using hz) with rfl | hzp
    · rfl
    · exact (hx₂No hzp hAdj).elim
  have hfull := hrTree.induce_insert_of_unique_adj hx₂NotR hyR hx₂y huniq
  have hrPath := r.isPath_of_length_eq_dist hrGeod
  have hcard : (insert x₂ r.support.toFinset).card = p.length + 2 := by
    rw [Finset.card_insert_of_notMem hx₂NotR,
      List.toFinset_card_of_nodup hrPath.support_nodup, Walk.length_support, hrLen]
  have hbound := hfull.card_le_largestInducedTreeSize_splice
  omega
omit [Fintype α] [DecidableEq α] in
/-- On a geodesic in a graph of girth at least four, two distinct neighbors of
one outside vertex occur exactly two indices apart. -/
lemma Walk.geodesic_outside_neighbor_index_gap_two_splice
    {b w y : α} (p : G.Walk b w) (hp : p.length = G.dist b w)
    (hy : y ∉ p.support) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hij : i ≠ j) (hyi : G.Adj y (p.getVert i))
    (hyj : G.Adj y (p.getVert j)) (hg : 4 ≤ G.girth) :
    i + 2 = j ∨ j + 2 = i := by
  have key : ∀ {i j : ℕ}, i ≤ p.length → j ≤ p.length → i < j →
      G.Adj y (p.getVert i) → G.Adj y (p.getVert j) → i + 2 = j := by
    intro i j hi hj hij hyi hyj
    let seg₀ := (p.drop i).take (j - i)
    have hsub : seg₀.IsSubwalk p :=
      (Walk.isSubwalk_take (p.drop i) (j - i)).trans (Walk.isSubwalk_drop p i)
    have hend : (p.drop i).getVert (j - i) = p.getVert j := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le (Nat.le_of_lt hij)]
    have hsegLen : seg₀.length = j - i := by
      dsimp [seg₀]
      rw [Walk.take_length, Walk.drop_length, Nat.min_eq_left (by omega)]
    have hsegGeod₀ := length_eq_dist_of_subwalk hp hsub
    have hsegGeod : seg₀.length = G.dist (p.getVert i) (p.getVert j) :=
      hsegGeod₀.trans (congrArg (G.dist (p.getVert i)) hend)
    have htwo : G.dist (p.getVert i) (p.getVert j) ≤ 2 := by
      let two : G.Walk (p.getVert i) (p.getVert j) :=
        Walk.cons hyi.symm (Walk.cons hyj Walk.nil)
      have := G.dist_le two
      simpa [two] using this
    have hsegPath := seg₀.isPath_of_length_eq_dist hsegGeod₀
    have hySeg : y ∉ seg₀.support := by
      intro hymem
      exact hy (hsub.support_subset hymem)
    have hyEnd : G.Adj ((p.drop i).getVert (j - i)) y := by
      rw [hend]
      exact hyj.symm
    have hendNe : p.getVert i ≠ (p.drop i).getVert (j - i) := by
      intro heq
      have hzero : G.dist (p.getVert i) ((p.drop i).getVert (j - i)) = 0 := by
        simp [heq]
      omega
    have hcycle : ((seg₀.concat hyEnd).concat hyi).IsCycle :=
      hsegPath.concat_two_isCycle_splice hendNe hySeg hyEnd hyi
    have hgLe := G.girth_le_length hcycle
    simp only [Walk.length_concat, hsegLen] at hgLe
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Or.inl (key hi hj hij hyi hyj)
  · exact Or.inr (key hj hi hji hyj hyi)
/-- L9: the complete girth-four hard branch. -/
lemma cyclic_girth_four_bound_splice [Nontrivial α] [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : G.girth = 4) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  let B : Set α := maxEccentricityVertices G
  let f := G.eccSet B
  change f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G
  rw [hg]
  norm_num
  have hfD : f + 1 ≤ G.diam := by
    simpa only [B, f] using
      eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  have hdiamTree := diam_add_one_le_largestInducedTreeSize_splice hconn
  by_cases heasy : f + 2 ≤ G.diam
  · omega
  have hDf : G.diam = f + 1 := by omega
  have hDthree := three_le_diam_of_girth_four_eccSet_pos_splice hconn hfpos hg
  obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  obtain ⟨hbB, hwB⟩ :=
    diametral_endpoints_mem_maxEccentricityVertices_splice hconn hbw
  have hfxb : f ≤ G.dist x b := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x b := distToSet_le_dist_of_mem_public (G := G) x hbB
  have hfxw : f ≤ G.dist x w := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x w := distToSet_le_dist_of_mem_public (G := G) x hwB
  obtain ⟨p, hpPath, hpLen⟩ := hconn.exists_path_of_dist b w
  have hpD : p.length = G.diam := hpLen.trans hbw
  have hxNotP : x ∉ p.support := by
    intro hxp
    obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp hxp
    have hleft₀ := G.dist_le (p.take i)
    have hleft : G.dist b x ≤ i := by
      simpa [Walk.take_length, Nat.min_eq_left hiLe, hiEq] using hleft₀
    have hright₀ := G.dist_le (p.drop i)
    have hright : G.dist x w ≤ p.length - i := by
      simpa [Walk.drop_length, hiEq] using hright₀
    have hfxb' : f ≤ G.dist b x := by simpa only [G.dist_comm] using hfxb
    omega
  let P : Set α := (p.support.toFinset : Set α)
  have hP : P.Nonempty := by exact ⟨b, by simp [P]⟩
  obtain ⟨k, hkP, q, hqPath, hq⟩ :=
    hconn.exists_path_length_eq_distToSet_splice x hP
  have hkSupport : k ∈ p.support := by simpa [P] using hkP
  have hqPos : 0 < q.length := by
    by_contra hnot
    have hzero : q.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hxk : x = k := q.eq_of_length_eq_zero hzero
    apply hxNotP
    simpa [hxk] using hkSupport
  have hqNotNil : ¬q.Nil := Walk.not_nil_iff_lt_length.mpr hqPos
  have hyK : G.Adj q.penultimate k := q.adj_penultimate hqNotNil
  have hyNotP : q.penultimate ∉ p.support := by
    intro hyP
    have hnot := q.getVert_not_mem_of_length_eq_distToSet hq
      (i := q.length - 1) (by omega)
    apply hnot
    simpa [P] using hyP
  by_cases huniq : ∀ ⦃a : α⦄, a ∈ p.support →
      G.Adj q.penultimate a → a = k
  · have hbound := p.geodesic_unique_attachment_tree_bound_splice
      hpLen hyNotP hkSupport hyK huniq
    omega
  push_neg at huniq
  obtain ⟨a, haP, hya, hak⟩ := huniq
  obtain ⟨i, hiEq, hiLe⟩ := Walk.mem_support_iff_exists_getVert.mp haP
  obtain ⟨j, hjEq, hjLe⟩ := Walk.mem_support_iff_exists_getVert.mp hkSupport
  have hij : i ≠ j := by
    intro hij
    apply hak
    calc
      a = p.getVert i := hiEq.symm
      _ = p.getVert j := by rw [hij]
      _ = k := hjEq
  have hyi : G.Adj q.penultimate (p.getVert i) := by simpa [hiEq] using hya
  have hyj : G.Adj q.penultimate (p.getVert j) := by simpa [hjEq] using hyK
  have hgap := p.geodesic_outside_neighbor_index_gap_two_splice
    hpLen hyNotP hiLe hjLe hij hyi hyj (by omega : 4 ≤ G.girth)
  have hqTwo : 2 ≤ q.length := by
    by_contra hnot
    have hqOne : q.length = 1 := by omega
    have hyEq : q.penultimate = x := by simp [Walk.penultimate, hqOne]
    have hxi : G.Adj x (p.getVert i) := by simpa [hyEq] using hyi
    have hxj : G.Adj x (p.getVert j) := by simpa [hyEq] using hyj
    rcases hgap with hgap | hgap
    · let left : G.Walk x b := Walk.cons hxi (p.take i).reverse
      have hleft₀ := G.dist_le left
      have hleft : G.dist x b ≤ i + 1 := by
        simpa [left, Walk.take_length, Nat.min_eq_left hiLe] using hleft₀
      let right : G.Walk x w := Walk.cons hxj (p.drop j)
      have hright₀ := G.dist_le right
      have hright : G.dist x w ≤ p.length - j + 1 := by
        simpa [right, Walk.drop_length] using hright₀
      omega
    · let left : G.Walk x b := Walk.cons hxj (p.take j).reverse
      have hleft₀ := G.dist_le left
      have hleft : G.dist x b ≤ j + 1 := by
        simpa [left, Walk.take_length, Nat.min_eq_left hjLe] using hleft₀
      let right : G.Walk x w := Walk.cons hxi (p.drop i)
      have hright₀ := G.dist_le right
      have hright : G.dist x w ≤ p.length - i + 1 := by
        simpa [right, Walk.drop_length] using hright₀
      omega
  let x₂ := q.getVert (q.length - 2)
  have hx₂y : G.Adj x₂ q.penultimate := by
    dsimp [x₂, Walk.penultimate]
    have hindex : q.length - 2 + 1 = q.length - 1 := by omega
    simpa only [hindex] using
      q.adj_getVert_succ (i := q.length - 2) (by omega)
  have hx₂NotP : x₂ ∉ p.support := by
    intro hx₂P
    have hnot := q.getVert_not_mem_of_length_eq_distToSet hq
      (i := q.length - 2) (by omega)
    apply hnot
    simpa [P, x₂] using hx₂P
  have hx₂Depth : G.distToSet x₂ P = 2 := by
    have hdepth := q.distToSet_getVert_eq_length_sub_of_nearest
      hconn hkP hq (i := q.length - 2) (by omega)
    dsimp [x₂]
    rw [hdepth]
    omega
  have hx₂No : ∀ ⦃z : α⦄, z ∈ p.support → ¬G.Adj x₂ z := by
    intro z hz hAdj
    have hzP : z ∈ P := by simpa [P] using hz
    have hsetLe := distToSet_le_dist_of_mem_public (G := G) x₂ hzP
    have hdistOne : G.dist x₂ z = 1 := dist_eq_one_iff_adj.mpr hAdj
    rw [hx₂Depth, hdistOne] at hsetLe
    omega
  rcases hgap with hgap | hgap
  · have hiy : G.Adj (p.getVert i) q.penultimate := hyi.symm
    have hyi₂ : G.Adj q.penultimate (p.getVert (i + 2)) := by
      rw [hgap]
      exact hyj
    have hbound := p.geodesic_two_step_reroute_tree_bound_splice
      hpLen (by omega) hyNotP hiy hyi₂ hx₂NotP hx₂y hx₂No
    omega
  · have hjy : G.Adj (p.getVert j) q.penultimate := hyj.symm
    have hyj₂ : G.Adj q.penultimate (p.getVert (j + 2)) := by
      rw [hgap]
      exact hyi
    have hbound := p.geodesic_two_step_reroute_tree_bound_splice
      hpLen (by omega) hyNotP hjy hyj₂ hx₂NotP hx₂y hx₂No
    omega
omit [Fintype α] [DecidableEq α] in
/-- Two ambient paths with the same endpoints and support inside one induced
tree are equal. -/
lemma IsTree.ambient_path_unique_of_support_subset_splice
    {S : Finset α} (hT : (G.induce (S : Set α)).IsTree)
    {u v : α} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hpS : ∀ x ∈ p.support, x ∈ (S : Set α))
    (hqS : ∀ x ∈ q.support, x ∈ (S : Set α)) : p = q := by
  have huS : u ∈ (S : Set α) := hpS u p.start_mem_support
  have hvS : v ∈ (S : Set α) := hpS v p.end_mem_support
  let uS : ↥(S : Set α) := ⟨u, huS⟩
  let vS : ↥(S : Set α) := ⟨v, hvS⟩
  let p₀ := p.induce (S : Set α) hpS
  let q₀ := q.induce (S : Set α) hqS
  let pᵢ : (G.induce (S : Set α)).Walk uS vS :=
    p₀.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  let qᵢ : (G.induce (S : Set α)).Walk uS vS :=
    q₀.copy (Subtype.ext (by rfl)) (Subtype.ext (by rfl))
  have hp₀ : p₀.IsPath := by
    apply (Walk.map_isPath_iff_of_injective
      (p := p₀)
      (f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).injective).mp
    change (p.induce (S : Set α) hpS).map
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom |>.IsPath
    rw [Walk.map_induce]
    exact hp
  have hq₀ : q₀.IsPath := by
    apply (Walk.map_isPath_iff_of_injective
      (p := q₀)
      (f := (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom)
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).injective).mp
    change (q.induce (S : Set α) hqS).map
      (SimpleGraph.Embedding.induce (G := G) (S : Set α)).toHom |>.IsPath
    rw [Walk.map_induce]
    exact hq
  have hpᵢ : pᵢ.IsPath := by
    dsimp [pᵢ]
    exact (Walk.isPath_copy p₀ (Subtype.ext (by rfl))
      (Subtype.ext (by rfl))).2 hp₀
  have hqᵢ : qᵢ.IsPath := by
    dsimp [qᵢ]
    exact (Walk.isPath_copy q₀ (Subtype.ext (by rfl))
      (Subtype.ext (by rfl))).2 hq₀
  have heq : pᵢ = qᵢ := by
    exact congrArg Subtype.val
      (hT.IsAcyclic.path_unique ⟨pᵢ, hpᵢ⟩ ⟨qᵢ, hqᵢ⟩)
  have hpMap : pᵢ.map (SimpleGraph.Embedding.induce (G := G)
      (S : Set α)).toHom = p := by
    dsimp [pᵢ, p₀]
    simpa using (Walk.map_induce (s := (S : Set α)) p hpS)
  have hqMap : qᵢ.map (SimpleGraph.Embedding.induce (G := G)
      (S : Set α)).toHom = q := by
    dsimp [qᵢ, q₀]
    simpa using (Walk.map_induce (s := (S : Set α)) q hqS)
  rw [← hpMap, ← hqMap, heq]

/-- Three positive nearest-cycle descents already yield one vertex more than a
retained girth cycle when all three terminal pairs are nontrivial. -/
lemma Walk.three_positive_descents_plus_one_bound_splice
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length) (htPos : 0 < t.length)
    (huv : 1 ≤ G.dist u v) (huw : 1 ≤ G.dist u w)
    (hvw : 1 ≤ G.dist v w) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  have hL8 := Walk.three_positive_descents_L8_dichotomy
    hc hcLength hg hconn p q t hku hkv hkw hp hq ht hpPos hqPos htPos
      (f := 1) huv huw hvw
  have hright : G.girth + 1 ≤
      G.girth - 1 + p.length + q.length + t.length := by omega
  exact (Nat.le_min.mpr ⟨by omega, hright⟩).trans hL8

/-- Two positive nearest-cycle descents whose terminals are distinct yield one
vertex more than a retained girth cycle. -/
lemma Walk.two_positive_descents_plus_one_bound_splice
    {z u ku v kv : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (hpPos : 0 < p.length) (hqPos : 0 < q.length)
    (huv : 1 ≤ G.dist u v) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  have hL8 := Walk.two_positive_descents_L8_dichotomy
    hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos (f := 1) huv
  have hright : G.girth + 1 ≤ G.girth - 1 + p.length + q.length := by omega
  exact (Nat.le_min.mpr ⟨by omega, hright⟩).trans hL8

/-- A sole positive descent yields `girth + 1`, unless L6 forces the selected
terminal distance sum below `girth + 3`. -/
lemma Walk.one_positive_descent_strong_sum_bound_splice
    {z u ku v w : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (hku : ku ∈ c.support)
    (hv : v ∈ c.support) (hw : w ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hpPos : 0 < p.length)
    (hlower : G.girth + 3 ≤ G.dist u v + G.dist u w + G.dist v w) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  have htree := Walk.one_descent_largestInducedTreeSize
    hc hcLength hg hconn p hku hp hpPos
  by_cases hpTwo : 2 ≤ p.length
  · omega
  · have hpOne : p.length = 1 := by omega
    have hL6 := hc.three_arc_inequality_splice hconn p
      (Walk.nil : G.Walk v v) (Walk.nil : G.Walk w w) hku hv hw
    rw [hcLength] at hL6
    simp at hL6
    omega

/-- Strong-sum L8 dispatcher.  If three terminals have pairwise positive
separation and total pairwise distance at least `girth + 3`, their nearest-cycle
descents force an induced tree on at least `girth + 1` vertices. -/
lemma Walk.three_descents_strong_sum_bound_splice
    {z u ku v kv w kw : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hg : 5 ≤ G.girth) (hconn : G.Connected)
    (p : G.Walk u ku) (q : G.Walk v kv) (t : G.Walk w kw)
    (hku : ku ∈ c.support) (hkv : kv ∈ c.support) (hkw : kw ∈ c.support)
    (hp : p.length = G.distToSet u (c.support.toFinset : Set α))
    (hq : q.length = G.distToSet v (c.support.toFinset : Set α))
    (ht : t.length = G.distToSet w (c.support.toFinset : Set α))
    (huv : 1 ≤ G.dist u v) (huw : 1 ≤ G.dist u w)
    (hvw : 1 ≤ G.dist v w)
    (hlower : G.girth + 3 ≤ G.dist u v + G.dist u w + G.dist v w) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  by_cases hpPos : 0 < p.length
  · by_cases hqPos : 0 < q.length
    · by_cases htPos : 0 < t.length
      · exact Walk.three_positive_descents_plus_one_bound_splice
          hc hcLength hg hconn p q t hku hkv hkw hp hq ht hpPos hqPos htPos
            huv huw hvw
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        exact Walk.two_positive_descents_plus_one_bound_splice
          hc hcLength hg hconn p q hku hkv hp hq hpPos hqPos huv
    · have hqZero : q.length = 0 := Nat.eq_zero_of_not_pos hqPos
      have hvEq : v = kv := q.eq_of_length_eq_zero hqZero
      have hvCycle : v ∈ c.support := by simpa [hvEq] using hkv
      by_cases htPos : 0 < t.length
      · exact Walk.two_positive_descents_plus_one_bound_splice
          hc hcLength hg hconn p t hku hkw hp ht hpPos htPos huw
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact Walk.one_positive_descent_strong_sum_bound_splice
          hc hcLength hg hconn p hku hvCycle hwCycle hp hpPos hlower
  · have hpZero : p.length = 0 := Nat.eq_zero_of_not_pos hpPos
    have huEq : u = ku := p.eq_of_length_eq_zero hpZero
    have huCycle : u ∈ c.support := by simpa [huEq] using hku
    by_cases hqPos : 0 < q.length
    · by_cases htPos : 0 < t.length
      · exact Walk.two_positive_descents_plus_one_bound_splice
          hc hcLength hg hconn q t hkv hkw hq ht hqPos htPos hvw
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        exact Walk.one_positive_descent_strong_sum_bound_splice
          hc hcLength hg hconn q hkv huCycle hwCycle hq hqPos
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
    · have hqZero : q.length = 0 := Nat.eq_zero_of_not_pos hqPos
      have hvEq : v = kv := q.eq_of_length_eq_zero hqZero
      have hvCycle : v ∈ c.support := by simpa [hvEq] using hkv
      by_cases htPos : 0 < t.length
      · exact Walk.one_positive_descent_strong_sum_bound_splice
          hc hcLength hg hconn t hkw huCycle hvCycle ht htPos
            (by simpa only [G.dist_comm, add_comm, add_left_comm, add_assoc] using hlower)
      · have htZero : t.length = 0 := Nat.eq_zero_of_not_pos htPos
        have hwEq : w = kw := t.eq_of_length_eq_zero htZero
        have hwCycle : w ∈ c.support := by simpa [hwEq] using hkw
        have hroot := hc.sum_three_dist_le_length_splice huCycle hvCycle hwCycle
        rw [hcLength] at hroot
        omega

omit [Fintype α] in
/-- If a girth-realizing cycle covers every vertex, each arc of length at most
half the cycle is geodesic.  The proof deletes a cycle vertex outside a
hypothetical shortcut and uses uniqueness of paths in the remaining induced
tree. -/
lemma Walk.IsCycle.take_geodesic_of_vertex_cover_splice
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hcover : ∀ x : α, x ∈ c.support) {h : ℕ}
    (hpos : 0 < h) (hhalf : 2 * h ≤ c.length) :
    G.dist z (c.getVert h) = h := by
  have hlt : h < c.length := by omega
  let short : G.Walk z (c.getVert h) := c.take h
  have hshortLen : short.length = h := by
    dsimp [short]
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hdistLe : G.dist z (c.getVert h) ≤ h := by
    simpa [hshortLen] using G.dist_le short
  by_contra hne
  have hdistLt : G.dist z (c.getVert h) < h := by omega
  obtain ⟨p, hpPath, hpLen⟩ := hconn.exists_path_of_dist z (c.getVert h)
  have hdropPos : 0 < (c.drop h).length := by
    rw [Walk.drop_length]
    omega
  have hshortPath : short.IsPath := by
    have hcycSplit : ((c.take h).append (c.drop h)).IsCycle := by
      rw [Walk.append_take_drop_eq]
      exact hc
    dsimp [short]
    exact hcycSplit.isPath_of_append_left
      (Walk.not_nil_iff_lt_length.mpr hdropPos)
  let C := c.support.toFinset
  let P := p.support.toFinset
  let A := short.support.toFinset
  have hcardC : C.card = c.length := by
    simpa [C] using hc.card_support_toFinset_eq_length_splice
  have hcardP : P.card = p.length + 1 := by
    dsimp [P]
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hcardA : A.card = h + 1 := by
    dsimp [A]
    rw [List.toFinset_card_of_nodup hshortPath.support_nodup,
      Walk.length_support, hshortLen]
  have hzr : z ≠ c.getVert h := by
    intro heq
    have hidx : (0 : ℕ) = h := by
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · simpa using heq
    omega
  have hpairSub : ({z, c.getVert h} : Finset α) ⊆ P ∩ A := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
  have hcardInter : 2 ≤ (P ∩ A).card := by
    have hle := Finset.card_le_card hpairSub
    simpa [hzr] using hle
  have hcardUnion := Finset.card_union_add_card_inter P A
  have hunionLt : (P ∪ A).card < C.card := by
    rw [hcardC]
    omega
  have hnotSub : ¬C ⊆ P ∪ A := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨erase, hEraseC, hEraseUnion⟩ := Finset.not_subset.mp hnotSub
  have hEraseP : erase ∉ P := by
    intro he
    exact hEraseUnion (Finset.mem_union_left A he)
  have hEraseA : erase ∉ A := by
    intro he
    exact hEraseUnion (Finset.mem_union_right P he)
  have hEraseCycle : erase ∈ c.support := by simpa [C] using hEraseC
  let rot := c.rotate hEraseCycle
  let base := rot.tail.dropLast
  have hbaseCert := hc.erase_vertex_path_certificate_splice hEraseCycle hcLength
  change base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase erase ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 at hbaseCert
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, _⟩
  have htree :
      (G.induce ((C.erase erase : Finset α) : Set α)).IsTree := by
    change (G.induce ((c.support.toFinset.erase erase : Finset α) : Set α)).IsTree
    rw [← hbaseSupport]
    exact hbaseTree
  have hpS : ∀ y ∈ p.support, y ∈ ((C.erase erase : Finset α) : Set α) := by
    intro y hy
    change y ∈ C.erase erase
    apply Finset.mem_erase.mpr
    constructor
    · intro hye
      subst y
      exact hEraseP (by simpa [P] using hy)
    · simpa [C] using hcover y
  have hshortS : ∀ y ∈ short.support,
      y ∈ ((C.erase erase : Finset α) : Set α) := by
    intro y hy
    change y ∈ C.erase erase
    apply Finset.mem_erase.mpr
    constructor
    · intro hye
      subst y
      exact hEraseA (by simpa [A] using hy)
    · have hyC := (Walk.isSubwalk_take c h).support_subset hy
      simpa [C] using hyC
  have heq := htree.ambient_path_unique_of_support_subset_splice
    p short hpPath hshortPath hpS hshortS
  have hlenEq := congrArg Walk.length heq
  omega

/-- A girth cycle covering the whole vertex set is the whole graph: every
vertex is peripheral, hence the eccentricity of the periphery is zero. -/
lemma Walk.IsCycle.eccSet_periphery_eq_zero_of_vertex_cover_splice
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hcover : ∀ x : α, x ∈ c.support) :
    G.eccSet (maxEccentricityVertices G) = 0 := by
  letI : Nonempty α := ⟨z⟩
  let H := c.length / 2
  have hHpos : 0 < H := by
    dsimp [H]
    have := hc.three_le_length
    omega
  have hhalf : 2 * H ≤ c.length := by
    dsimp [H]
    omega
  have hpairUpper : ∀ u v : α, G.dist u v ≤ H := by
    intro u v
    have hs := hc.sum_three_dist_le_length_splice
      (hcover u) (hcover v) (hcover u)
    have hself : G.dist u u = 0 := by simp
    have hsym : G.dist v u = G.dist u v := G.dist_comm
    rw [hself, add_zero, hsym] at hs
    dsimp [H]
    omega
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  have hdiamLe : G.diam ≤ H := by
    rw [← hbw]
    exact hpairUpper b w
  have hzHalf : G.dist z (c.getVert H) = H :=
    hc.take_geodesic_of_vertex_cover_splice hcLength hconn hcover hHpos hhalf
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hdiamGe : H ≤ G.diam := by
    rw [← hzHalf]
    exact dist_le_diam hfinite
  have hdiam : G.diam = H := Nat.le_antisymm hdiamLe hdiamGe
  have hperipheral : ∀ u : α, u ∈ maxEccentricityVertices G := by
    intro u
    have hu : u ∈ c.support := hcover u
    let rot := c.rotate hu
    have hrotCycle : rot.IsCycle := by
      dsimp [rot]
      exact hc.rotate hu
    have hrotLength : rot.length = G.girth := by
      dsimp [rot]
      exact (c.length_rotate_splice hu).trans hcLength
    have hrotCover : ∀ x : α, x ∈ rot.support := by
      intro x
      dsimp [rot]
      exact (c.mem_support_rotate_iff hu).mpr (hcover x)
    have hrotHalf : 2 * H ≤ rot.length := by
      rw [hrotLength, ← hcLength]
      exact hhalf
    have hur : G.dist u (rot.getVert H) = H :=
      hrotCycle.take_geodesic_of_vertex_cover_splice
        hrotLength hconn hrotCover hHpos hrotHalf
    have hdiamPair : G.dist u (rot.getVert H) = G.diam := by
      rw [hur, hdiam]
    exact (diametral_endpoints_mem_maxEccentricityVertices_splice
      hconn hdiamPair).1
  let B : Set α := maxEccentricityVertices G
  have hdistZero : ∀ u : α, G.distToSet u B = 0 := by
    intro u
    apply Nat.eq_zero_of_le_zero
    have hle := distToSet_le_dist_of_mem_public (G := G) u (hperipheral u)
    simpa [B] using hle
  have himage : Finset.univ.image (fun u : α => G.distToSet u B) = {0} := by
    ext n
    simp [hdistZero]
    omega
  unfold eccSet
  rw [himage]
  simp

omit [Fintype α] in
/-- A half-cycle arc remains geodesic after adjoining one vertex with a unique
attachment at the initial cycle vertex. -/
lemma Walk.IsCycle.take_geodesic_of_unique_one_vertex_extension_splice
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hxOut : x ∉ c.support)
    (hcover : ∀ y : α, y ∈ c.support ∨ y = x)
    (hxz : G.Adj x z)
    (hxUnique : ∀ ⦃y : α⦄, y ∈ c.support → G.Adj x y → y = z)
    {h : ℕ} (hpos : 0 < h) (hhalf : 2 * h ≤ c.length) :
    G.dist z (c.getVert h) = h := by
  have hlt : h < c.length := by omega
  let short : G.Walk z (c.getVert h) := c.take h
  have hshortLen : short.length = h := by
    dsimp [short]
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hdistLe : G.dist z (c.getVert h) ≤ h := by
    simpa [hshortLen] using G.dist_le short
  by_contra hne
  have hdistLt : G.dist z (c.getVert h) < h := by omega
  obtain ⟨p, hpPath, hpLen⟩ := hconn.exists_path_of_dist z (c.getVert h)
  have hdropPos : 0 < (c.drop h).length := by
    rw [Walk.drop_length]
    omega
  have hshortPath : short.IsPath := by
    have hcycSplit : ((c.take h).append (c.drop h)).IsCycle := by
      rw [Walk.append_take_drop_eq]
      exact hc
    dsimp [short]
    exact hcycSplit.isPath_of_append_left
      (Walk.not_nil_iff_lt_length.mpr hdropPos)
  let C := c.support.toFinset
  let P := p.support.toFinset
  let A := short.support.toFinset
  have hcardC : C.card = c.length := by
    simpa [C] using hc.card_support_toFinset_eq_length_splice
  have hcardP : P.card = p.length + 1 := by
    dsimp [P]
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, Walk.length_support]
  have hcardA : A.card = h + 1 := by
    dsimp [A]
    rw [List.toFinset_card_of_nodup hshortPath.support_nodup,
      Walk.length_support, hshortLen]
  have hzr : z ≠ c.getVert h := by
    intro heq
    have hidx : (0 : ℕ) = h := by
      apply hc.getVert_injOn'
      · simp only [Set.mem_setOf_eq]
        omega
      · simp only [Set.mem_setOf_eq]
        omega
      · simpa using heq
    omega
  have hpairSub : ({z, c.getVert h} : Finset α) ⊆ P ∩ A := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
    · exact Finset.mem_inter.mpr ⟨by simp [P], by simp [A, short]⟩
  have hcardInter : 2 ≤ (P ∩ A).card := by
    have hle := Finset.card_le_card hpairSub
    simpa [hzr] using hle
  have hcardUnion := Finset.card_union_add_card_inter P A
  have hunionLt : (P ∪ A).card < C.card := by
    rw [hcardC]
    omega
  have hnotSub : ¬C ⊆ P ∪ A := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨erase, hEraseC, hEraseUnion⟩ := Finset.not_subset.mp hnotSub
  have hEraseP : erase ∉ P := by
    intro he
    exact hEraseUnion (Finset.mem_union_left A he)
  have hEraseA : erase ∉ A := by
    intro he
    exact hEraseUnion (Finset.mem_union_right P he)
  have hEraseCycle : erase ∈ c.support := by simpa [C] using hEraseC
  let rot := c.rotate hEraseCycle
  let base := rot.tail.dropLast
  have hbaseCert := hc.erase_vertex_path_certificate_splice hEraseCycle hcLength
  change base.IsPath ∧
      base.support.toFinset = c.support.toFinset.erase erase ∧
      (G.induce (base.support.toFinset : Set α)).IsTree ∧
      base.support.toFinset.card = c.length - 1 at hbaseCert
  rcases hbaseCert with ⟨_, hbaseSupport, hbaseTree, _⟩
  have hbaseTree' :
      (G.induce ((C.erase erase : Finset α) : Set α)).IsTree := by
    change (G.induce ((c.support.toFinset.erase erase : Finset α) : Set α)).IsTree
    rw [← hbaseSupport]
    exact hbaseTree
  have hxNotBase : x ∉ C.erase erase := by
    intro hx
    exact hxOut (by simpa [C] using (Finset.mem_of_mem_erase hx))
  have hzBase : z ∈ C.erase erase := by
    apply Finset.mem_erase.mpr
    constructor
    · intro hze
      subst erase
      exact hEraseA (by simp [A, short])
    · simp [C]
  have hfullTree := hbaseTree'.induce_insert_of_unique_adj
    hxNotBase hzBase hxz (by
      intro y hy hxy
      apply hxUnique
      · have hyC : y ∈ C := Finset.mem_of_mem_erase (by simpa using hy)
        simpa [C] using hyC
      · exact hxy)
  let S : Finset α := insert x (C.erase erase)
  have hpS : ∀ y ∈ p.support, y ∈ (S : Set α) := by
    intro y hy
    change y ∈ S
    rcases hcover y with hyC | rfl
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_erase.mpr
      constructor
      · intro hye
        subst y
        exact hEraseP (by simpa [P] using hy)
      · simpa [C] using hyC
    · exact Finset.mem_insert_self _ _
  have hshortS : ∀ y ∈ short.support, y ∈ (S : Set α) := by
    intro y hy
    change y ∈ S
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_erase.mpr
    constructor
    · intro hye
      subst y
      exact hEraseA (by simpa [A] using hy)
    · have hyC := (Walk.isSubwalk_take c h).support_subset hy
      simpa [C] using hyC
  have htreeS : (G.induce (S : Set α)).IsTree := by
    simpa [S] using hfullTree
  have heq := htreeS.ambient_path_unique_of_support_subset_splice
    p short hpPath hshortPath hpS hshortS
  have hlenEq := congrArg Walk.length heq
  omega

omit [Fintype α] in
/-- In a one-vertex extension with a unique attachment, the pendant vertex is
one step farther from a half-cycle endpoint than the attachment vertex. -/
lemma Walk.IsCycle.dist_pendant_getVert_of_unique_one_vertex_extension_splice
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hxOut : x ∉ c.support)
    (hcover : ∀ y : α, y ∈ c.support ∨ y = x)
    (hxz : G.Adj x z)
    (hxUnique : ∀ ⦃y : α⦄, y ∈ c.support → G.Adj x y → y = z)
    {h : ℕ} (hpos : 0 < h) (hhalf : 2 * h ≤ c.length) :
    G.dist x (c.getVert h) = h + 1 := by
  have hzr := hc.take_geodesic_of_unique_one_vertex_extension_splice
    hcLength hconn hxOut hcover hxz hxUnique hpos hhalf
  have hlt : h < c.length := by omega
  let short : G.Walk z (c.getVert h) := c.take h
  have hshortLen : short.length = h := by
    dsimp [short]
    rw [Walk.take_length, Nat.min_eq_left (Nat.le_of_lt hlt)]
  let xp : G.Walk x (c.getVert h) := Walk.cons hxz short
  have hupper₀ := G.dist_le xp
  have hupper : G.dist x (c.getVert h) ≤ h + 1 := by
    simpa [xp, hshortLen] using hupper₀
  have hxr : x ≠ c.getVert h := by
    intro heq
    apply hxOut
    rw [heq]
    exact c.getVert_mem_support h
  obtain ⟨p, _, hpLen⟩ := hconn.exists_path_of_dist x (c.getVert h)
  have hpNotNil : ¬p.Nil := not_nil_of_ne hxr
  have huniqAll : ∀ ⦃y : α⦄, G.Adj x y → y = z := by
    intro y hxy
    rcases hcover y with hyC | rfl
    · exact hxUnique hyC hxy
    · exact (G.loopless _ hxy).elim
  have hsnd : p.snd = z := huniqAll (p.adj_snd hpNotNil)
  have htailDist₀ := G.dist_le p.tail
  have htailDist : G.dist z (c.getVert h) ≤ p.tail.length := by
    simpa [hsnd] using htailDist₀
  have htailLen : p.tail.length + 1 = p.length :=
    p.length_tail_add_one hpNotNil
  omega

/-- Global strong-sum closure: an eccentricity realizer together with a
diametral pair has enough total separation to invoke the strong L8 dispatcher. -/
lemma cyclic_strong_terminal_sum_bound_splice [Nontrivial α]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : 5 ≤ G.girth)
    (hsum : G.girth + 3 ≤
      2 * G.eccSet (maxEccentricityVertices G) + G.diam) :
    G.girth + 1 ≤ largestInducedTreeSize G := by
  let B : Set α := maxEccentricityVertices G
  let f := G.eccSet B
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  have hcycleSet : ((c.support.toFinset : Finset α) : Set α).Nonempty :=
    ⟨z, by simp⟩
  obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  obtain ⟨hbB, hwB⟩ :=
    diametral_endpoints_mem_maxEccentricityVertices_splice hconn hbw
  have hfxb : f ≤ G.dist x b := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x b := distToSet_le_dist_of_mem_public (G := G) x hbB
  have hfxw : f ≤ G.dist x w := by
    calc
      f = G.distToSet x B := hx.symm
      _ ≤ G.dist x w := distToSet_le_dist_of_mem_public (G := G) x hwB
  have hfD : f + 1 ≤ G.diam := by
    simpa only [B, f] using
      eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  have hbwOne : 1 ≤ G.dist b w := by rw [hbw]; omega
  have hxbOne : 1 ≤ G.dist x b := by
    have hfOne : 1 ≤ f := by simpa only [B, f] using hfpos
    omega
  have hxwOne : 1 ≤ G.dist x w := by
    have hfOne : 1 ≤ f := by simpa only [B, f] using hfpos
    omega
  have hlower : G.girth + 3 ≤
      G.dist x b + G.dist x w + G.dist b w := by
    rw [hbw]
    have hsum' : G.girth + 3 ≤ 2 * f + G.diam := by
      simpa only [B, f] using hsum
    omega
  obtain ⟨kx, hkx, p, _, hp⟩ :=
    hconn.exists_path_length_eq_distToSet_splice x hcycleSet
  obtain ⟨kb, hkb, q, _, hq⟩ :=
    hconn.exists_path_length_eq_distToSet_splice b hcycleSet
  obtain ⟨kw, hkw, t, _, ht⟩ :=
    hconn.exists_path_length_eq_distToSet_splice w hcycleSet
  have hkx' : kx ∈ c.support := by simpa using hkx
  have hkb' : kb ∈ c.support := by simpa using hkb
  have hkw' : kw ∈ c.support := by simpa using hkw
  exact Walk.three_descents_strong_sum_bound_splice
    hc hcLength hg hconn p q t hkx' hkb' hkw' hp hq ht
      hxbOne hxwOne hbwOne hlower

/-- The exceptional five-cycle with one pendant vertex has periphery eccentricity
at most one.  Its pendant and the two opposite cycle vertices are peripheral. -/
lemma Walk.IsCycle.eccSet_periphery_le_one_of_unique_one_vertex_extension_five_splice
    {z x : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hcFive : c.length = 5)
    (hconn : G.Connected)
    (hxOut : x ∉ c.support)
    (hcover : ∀ y : α, y ∈ c.support ∨ y = x)
    (hxz : G.Adj x z)
    (hxUnique : ∀ ⦃y : α⦄, y ∈ c.support → G.Adj x y → y = z) :
    G.eccSet (maxEccentricityVertices G) ≤ 1 := by
  letI : Nonempty α := ⟨x⟩
  have hdist2 : G.dist x (c.getVert 2) = 3 := by
    have h := hc.dist_pendant_getVert_of_unique_one_vertex_extension_splice
      hcLength hconn hxOut hcover hxz hxUnique (h := 2) (by omega) (by omega)
    omega
  have hcr : c.reverse.IsCycle := hc.reverse
  have hcrLength : c.reverse.length = G.girth := by
    rw [Walk.length_reverse]
    exact hcLength
  have hxOutR : x ∉ c.reverse.support := by simpa using hxOut
  have hcoverR : ∀ y : α, y ∈ c.reverse.support ∨ y = x := by
    intro y
    rcases hcover y with hy | hy
    · exact Or.inl (by simpa using hy)
    · exact Or.inr hy
  have hxUniqueR : ∀ ⦃y : α⦄, y ∈ c.reverse.support → G.Adj x y → y = z := by
    intro y hy hxy
    apply hxUnique (by simpa using hy) hxy
  have hdistRev : G.dist x (c.reverse.getVert 2) = 3 := by
    have h := hcr.dist_pendant_getVert_of_unique_one_vertex_extension_splice
      hcrLength hconn hxOutR hcoverR hxz hxUniqueR
        (h := 2) (by omega) (by simp [hcFive])
    omega
  have hrevVert : c.reverse.getVert 2 = c.getVert 3 := by
    rw [Walk.getVert_reverse, hcFive]
  have hdist3 : G.dist x (c.getVert 3) = 3 := by
    rw [← hrevVert]
    exact hdistRev
  have hcyclePair : ∀ ⦃u v : α⦄, u ∈ c.support → v ∈ c.support →
      G.dist u v ≤ 2 := by
    intro u v hu hv
    have hs := hc.sum_three_dist_le_length_splice hu hv hu
    have hself : G.dist u u = 0 := by simp
    have hsym : G.dist v u = G.dist u v := G.dist_comm
    rw [hself, add_zero, hsym, hcFive] at hs
    omega
  have hxzDist : G.dist x z = 1 := dist_eq_one_iff_adj.mpr hxz
  have hpairUpper : ∀ u v : α, G.dist u v ≤ 3 := by
    intro u v
    rcases hcover u with hu | hu
    · rcases hcover v with hv | hv
      · exact (hcyclePair hu hv).trans (by omega)
      · rw [hv, G.dist_comm]
        have htri := hconn.dist_triangle (u := x) (v := z) (w := u)
        have hzu := hcyclePair c.start_mem_support hu
        omega
    · rcases hcover v with hv | hv
      · rw [hu]
        have htri := hconn.dist_triangle (u := x) (v := z) (w := v)
        have hzv := hcyclePair c.start_mem_support hv
        omega
      · simp [hu, hv]
  obtain ⟨b, w, hbw⟩ := G.exists_dist_eq_diam
  have hdiamLe : G.diam ≤ 3 := by
    rw [← hbw]
    exact hpairUpper b w
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
  have hdiamGe : 3 ≤ G.diam := by
    rw [← hdist2]
    exact dist_le_diam hfinite
  have hdiam : G.diam = 3 := Nat.le_antisymm hdiamLe hdiamGe
  have hpair2 : G.dist x (c.getVert 2) = G.diam := by omega
  have hpair3 : G.dist x (c.getVert 3) = G.diam := by omega
  have hxB : x ∈ maxEccentricityVertices G :=
    (diametral_endpoints_mem_maxEccentricityVertices_splice hconn hpair2).1
  have h2B : c.getVert 2 ∈ maxEccentricityVertices G :=
    (diametral_endpoints_mem_maxEccentricityVertices_splice hconn hpair2).2
  have h3B : c.getVert 3 ∈ maxEccentricityVertices G :=
    (diametral_endpoints_mem_maxEccentricityVertices_splice hconn hpair3).2
  let B : Set α := maxEccentricityVertices G
  have hpoint : ∀ v : α, G.distToSet v B ≤ 1 := by
    intro v
    rcases hcover v with hvC | hvx
    · obtain ⟨i, hi, hiv⟩ := hc.exists_index_lt_getVert_splice hvC
      rw [hcFive] at hi
      subst v
      interval_cases i
      · have hle := distToSet_le_dist_of_mem_public (G := G) (c.getVert 0) hxB
        have hd : G.dist (c.getVert 0) x = 1 := by
          apply dist_eq_one_iff_adj.mpr
          simpa using hxz.symm
        exact hle.trans_eq hd
      · have hle := distToSet_le_dist_of_mem_public (G := G) (c.getVert 1) h2B
        have hd : G.dist (c.getVert 1) (c.getVert 2) = 1 :=
          dist_eq_one_iff_adj.mpr (c.adj_getVert_succ (by omega))
        simpa [B, hd] using hle
      · have hle := distToSet_le_dist_of_mem_public (G := G) (c.getVert 2) h2B
        have hzero : G.distToSet (c.getVert 2) B = 0 := by simpa [B] using hle
        omega
      · have hle := distToSet_le_dist_of_mem_public (G := G) (c.getVert 3) h3B
        have hzero : G.distToSet (c.getVert 3) B = 0 := by simpa [B] using hle
        omega
      · have hle := distToSet_le_dist_of_mem_public (G := G) (c.getVert 4) h3B
        have hd : G.dist (c.getVert 4) (c.getVert 3) = 1 :=
          dist_eq_one_iff_adj.mpr (c.adj_getVert_succ (by omega)).symm
        simpa [B, hd] using hle
    · rw [hvx]
      have hle := distToSet_le_dist_of_mem_public (G := G) x hxB
      have hzero : G.distToSet x B = 0 := by simpa [B] using hle
      omega
  obtain ⟨v, hv⟩ := exists_eccSet_witness_splice (G := G) B
  rw [← hv]
  exact hpoint v

/-- Positive distance from the periphery forces every girth cycle to omit a
vertex; otherwise the cycle-cover lemma makes every vertex peripheral. -/
lemma Walk.IsCycle.exists_not_mem_support_of_eccSet_pos_splice
    {z : α} {c : G.Walk z z} (hc : c.IsCycle)
    (hcLength : c.length = G.girth) (hconn : G.Connected)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G)) :
    ∃ x : α, x ∉ c.support := by
  by_contra hno
  simp only [not_exists, not_not] at hno
  have hzero := hc.eccSet_periphery_eq_zero_of_vertex_cover_splice
    hcLength hconn hno
  omega

/-- L10, residue `q = 1`: one nontrivial nearest-cycle descent adds the one
vertex needed beyond a cycle with one vertex erased. -/
lemma cyclic_residue_one_bound_splice [Nontrivial α]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic) (hg : 5 ≤ G.girth)
    (hfEq : G.eccSet (maxEccentricityVertices G) = G.girth / 3) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  have hfpos : 0 < G.eccSet (maxEccentricityVertices G) := by
    rw [hfEq]
    omega
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  obtain ⟨x, hxOut⟩ :=
    hc.exists_not_mem_support_of_eccSet_pos_splice hcLength hconn hfpos
  have hcycleSet : ((c.support.toFinset : Finset α) : Set α).Nonempty :=
    ⟨z, by simp⟩
  obtain ⟨kx, hkx, p, _, hp⟩ :=
    hconn.exists_path_length_eq_distToSet_splice x hcycleSet
  have hkx' : kx ∈ c.support := by simpa using hkx
  have hpPos : 0 < p.length := by
    by_contra hnot
    have hpZero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hxk : x = kx := p.eq_of_length_eq_zero hpZero
    apply hxOut
    simpa [hxk] using hkx'
  have htree := Walk.one_descent_largestInducedTreeSize
    hc hcLength hg hconn p hkx' hp hpPos
  omega

/-- L10, residue `q = 2`: this is the sole class `girth = 3m+2` and
`eccSet(periphery) = m+1`.  Strong terminal separation closes large diameter;
the remaining equality case is closed by two outside descents or the explicit
one-pendant metric. -/
lemma cyclic_residue_two_bound_splice [Nontrivial α]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic) (hg : 5 ≤ G.girth)
    {m : ℕ} (hgEq : G.girth = 3 * m + 2)
    (hfEq : G.eccSet (maxEccentricityVertices G) = m + 1) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  have hmPos : 0 < m := by omega
  have hfpos : 0 < G.eccSet (maxEccentricityVertices G) := by
    rw [hfEq]
    omega
  have htarget :
      G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) =
        G.girth + 1 := by
    rw [hgEq, hfEq]
    omega
  rw [htarget]
  have hfD :=
    eccSet_maxEccentricityVertices_add_one_le_diam_splice hconn hfpos
  by_cases hDstrong : m + 3 ≤ G.diam
  · have hsum : G.girth + 3 ≤
        2 * G.eccSet (maxEccentricityVertices G) + G.diam := by
      rw [hgEq, hfEq]
      omega
    exact cyclic_strong_terminal_sum_bound_splice
      hconn hcyc hfpos hg hsum
  have hD : G.diam = m + 2 := by
    rw [hfEq] at hfD
    omega
  obtain ⟨z, c, hc, hgirth⟩ := G.exists_girth_eq_length.mpr hcyc
  have hcLength : c.length = G.girth := hgirth.symm
  obtain ⟨x, hxOut⟩ :=
    hc.exists_not_mem_support_of_eccSet_pos_splice hcLength hconn hfpos
  have hcycleSet : ((c.support.toFinset : Finset α) : Set α).Nonempty :=
    ⟨z, by simp⟩
  obtain ⟨kx, hkx, p, _, hp⟩ :=
    hconn.exists_path_length_eq_distToSet_splice x hcycleSet
  have hkx' : kx ∈ c.support := by simpa using hkx
  have hpPos : 0 < p.length := by
    by_contra hnot
    have hpZero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hxk : x = kx := p.eq_of_length_eq_zero hpZero
    apply hxOut
    simpa [hxk] using hkx'
  by_cases hpTwo : 2 ≤ p.length
  · have htree := Walk.one_descent_largestInducedTreeSize
      hc hcLength hg hconn p hkx' hp hpPos
    omega
  have hpOne : p.length = 1 := by omega
  by_cases hsecond : ∃ y : α, y ∉ c.support ∧ y ≠ x
  · obtain ⟨y, hyOut, hyx⟩ := hsecond
    obtain ⟨ky, hky, q, _, hq⟩ :=
      hconn.exists_path_length_eq_distToSet_splice y hcycleSet
    have hky' : ky ∈ c.support := by simpa using hky
    have hqPos : 0 < q.length := by
      by_contra hnot
      have hqZero : q.length = 0 := Nat.eq_zero_of_not_pos hnot
      have hyk : y = ky := q.eq_of_length_eq_zero hqZero
      apply hyOut
      simpa [hyk] using hky'
    have hxyOne : 1 ≤ G.dist x y := hconn.pos_dist_of_ne hyx.symm
    exact Walk.two_positive_descents_plus_one_bound_splice
      hc hcLength hg hconn p q hkx' hky' hp hq hpPos hqPos hxyOne
  have hcover : ∀ y : α, y ∈ c.support ∨ y = x := by
    intro y
    by_cases hy : y ∈ c.support
    · exact Or.inl hy
    · right
      by_contra hyx
      exact hsecond ⟨y, hy, hyx⟩
  obtain ⟨hpPen, _, hpAdj, hpUnique⟩ :=
    Walk.nearest_cycle_dropLast_unique_attachment
      hc hcLength hg hconn p hkx' hp hpPos
  have hpen : p.penultimate = x := by
    change p.getVert (p.length - 1) = x
    rw [hpOne]
    simp
  have hxkx : G.Adj x kx := by simpa [hpen] using hpAdj
  have hxUnique : ∀ ⦃y : α⦄, y ∈ c.support → G.Adj x y → y = kx := by
    intro y hy hxy
    have hAdj : G.Adj p.penultimate y := by simpa [hpen] using hxy
    exact (hpUnique hpPen (by simpa using hy) hAdj).2
  let r := c.rotate hkx'
  have hrCycle : r.IsCycle := by
    dsimp [r]
    exact hc.rotate hkx'
  have hrLength : r.length = G.girth := by
    dsimp [r]
    exact (c.length_rotate_splice hkx').trans hcLength
  have hxOutR : x ∉ r.support := by
    intro hx
    apply hxOut
    dsimp [r] at hx
    exact (c.mem_support_rotate_iff hkx').mp hx
  have hcoverR : ∀ y : α, y ∈ r.support ∨ y = x := by
    intro y
    rcases hcover y with hy | hy
    · left
      dsimp [r]
      exact (c.mem_support_rotate_iff hkx').mpr hy
    · exact Or.inr hy
  have hxUniqueR : ∀ ⦃y : α⦄, y ∈ r.support → G.Adj x y → y = kx := by
    intro y hy hxy
    apply hxUnique
    · dsimp [r] at hy
      exact (c.mem_support_rotate_iff hkx').mp hy
    · exact hxy
  by_cases hmOne : m = 1
  · have hrFive : r.length = 5 := by
      rw [hrLength, hgEq, hmOne]
    have hsmall :=
      hrCycle.eccSet_periphery_le_one_of_unique_one_vertex_extension_five_splice
        hrLength hrFive hconn hxOutR hcoverR hxkx hxUniqueR
    rw [hfEq, hmOne] at hsmall
    norm_num at hsmall
  · have hmTwo : 2 ≤ m := by omega
    let H := r.length / 2
    have hHpos : 0 < H := by
      dsimp [H]
      rw [hrLength, hgEq]
      omega
    have hhalf : 2 * H ≤ r.length := by
      dsimp [H]
      omega
    have hfar :=
      hrCycle.dist_pendant_getVert_of_unique_one_vertex_extension_splice
        hrLength hconn hxOutR hcoverR hxkx hxUniqueR hHpos hhalf
    have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
    have hfarLe : G.dist x (r.getVert H) ≤ G.diam := dist_le_diam hfinite
    have hrForm : r.length = 3 * m + 2 := hrLength.trans hgEq
    rw [hD] at hfarLe
    dsimp [H] at hfar hfarLe
    omega

/-- Assembly of the `girth ≥ 5` positive-eccentricity branch from the small
range, the L8 main range, and the two L10 residue boxes. -/
lemma cyclic_girth_ge_five_positive_bound_splice [Nontrivial α]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G))
    (hg : 5 ≤ G.girth) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  let f := G.eccSet (maxEccentricityVertices G)
  change f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G
  by_cases hsmall : f ≤ G.girth / 3 - 1
  · exact cyclic_small_f_bound_splice hcyc hsmall
  have hfLower : G.girth / 3 ≤ f := by omega
  by_cases hmain : G.girth - 2 * (G.girth / 3) ≤ f
  · exact cyclic_main_range_bound_splice hconn hcyc
      (by simpa only [f] using hfpos) hg hmain
  have hdecomp := Nat.mod_add_div G.girth 3
  have hrem : G.girth % 3 < 3 := Nat.mod_lt _ (by omega)
  by_cases hfOne : f = G.girth / 3
  · exact cyclic_residue_one_bound_splice hconn hcyc hg (by
      simpa only [f] using hfOne)
  have hfTwo : f = G.girth / 3 + 1 := by omega
  have hgTwo : G.girth = 3 * (G.girth / 3) + 2 := by omega
  exact cyclic_residue_two_bound_splice hconn hcyc hg hgTwo (by
    simpa only [f] using hfTwo)

/-- The complete cyclic hard branch in integral form. -/
lemma cyclic_positive_integral_bound_splice [Nontrivial α] [DecidableRel G.Adj]
    (hconn : G.Connected) (hcyc : ¬G.IsAcyclic)
    (hfpos : 0 < G.eccSet (maxEccentricityVertices G)) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  have hg3 : 3 ≤ G.girth := three_le_girth hcyc
  by_cases hthree : G.girth = 3
  · exact cyclic_girth_three_bound_splice hconn hfpos hthree
  by_cases hfour : G.girth = 4
  · exact cyclic_girth_four_bound_splice hconn hfpos hfour
  have hg5 : 5 ≤ G.girth := by omega
  exact cyclic_girth_ge_five_positive_bound_splice hconn hcyc hfpos hg5

/-- Complete integral strengthening of Graffiti.pc Conjecture 142. -/
theorem conjecture142_integral_splice [Nontrivial α] [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.eccSet (maxEccentricityVertices G) + (G.girth - G.girth / 3) ≤
      largestInducedTreeSize G := by
  by_cases hacyc : G.IsAcyclic
  · have hgZero : G.girth = 0 := hacyc.girth_eq_zero
    let B : Set α := maxEccentricityVertices G
    let f := G.eccSet B
    obtain ⟨x, hx⟩ := exists_eccSet_witness_splice (G := G) B
    obtain ⟨b, hb⟩ := maxEccentricityVertices_nonempty_splice (G := G)
    have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hconn
    have hfD : f ≤ G.diam := by
      calc
        f = G.distToSet x B := hx.symm
        _ ≤ G.dist x b := distToSet_le_dist_of_mem_public (G := G) x hb
        _ ≤ G.diam := dist_le_diam hfinite
    have htree := diam_add_one_le_largestInducedTreeSize_splice hconn
    change f + (G.girth - G.girth / 3) ≤ largestInducedTreeSize G
    rw [hgZero]
    omega
  · by_cases hfZero : G.eccSet (maxEccentricityVertices G) = 0
    · have hg3 : 3 ≤ G.girth := three_le_girth hacyc
      have hsmall := cyclic_small_f_bound_splice (G := G) hacyc
        (f := 0) (by omega)
      simpa [hfZero] using hsmall
    · exact cyclic_positive_integral_bound_splice hconn hacyc
        (Nat.pos_of_ne_zero hfZero)

/-- Graffiti.pc Conjecture 142 in its exact real-valued Formal Conjectures
statement. -/
theorem conjecture142_real_splice [Nontrivial α] [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (2 : ℝ) / 3 * (G.girth : ℝ) +
        (G.eccSet (maxEccentricityVertices G) : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  have hint := conjecture142_integral_splice (G := G) hconn
  have hdiv : G.girth / 3 ≤ G.girth := Nat.div_le_self _ _
  have hcast :
      ((G.eccSet (maxEccentricityVertices G) +
        (G.girth - G.girth / 3) : ℕ) : ℝ) ≤
        (largestInducedTreeSize G : ℝ) := by
    exact_mod_cast hint
  rw [Nat.cast_add, Nat.cast_sub hdiv] at hcast
  have hceilNat :
      2 * G.girth ≤ 3 * (G.girth - G.girth / 3) := by omega
  have hceil :
      (2 : ℝ) * (G.girth : ℝ) ≤
        3 * ((G.girth - G.girth / 3 : ℕ) : ℝ) := by
    exact_mod_cast hceilNat
  rw [Nat.cast_sub hdiv] at hceil
  nlinarith
end SimpleGraph

namespace FormalProofs.WrittenOnTheWallII.GraphConjecture142

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII Conjecture 142: the largest induced tree has order at least two thirds
of the girth plus the eccentricity of the graph periphery. -/
theorem conjecture142 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let B : Set α := (maxEccentricityVertices G : Set α)
    (2 : ℝ) / 3 * (G.girth : ℝ) + (eccSet G B : ℝ) ≤
      (largestInducedTreeSize G : ℝ) := by
  dsimp
  exact SimpleGraph.conjecture142_real_splice (G := G) h

end FormalProofs.WrittenOnTheWallII.GraphConjecture142
