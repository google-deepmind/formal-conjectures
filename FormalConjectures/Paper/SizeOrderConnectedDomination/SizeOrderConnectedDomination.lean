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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture2

/-!
# Size, Order, and Connected Domination

*Reference:*
[S. Mukwembi, Size, Order, and Connected Domination,
Canad. Math. Bull. 57 (2014), no. 1, 141–144.](https://doi.org/10.4153/CMB-2013-020-5)

This paper gives a sharp upper bound on the size of a triangle-free graph
of a given order and connected domination number. As corollaries, it settles
a long-standing conjecture of Graffiti on the leaf number and local
independence for triangle-free graphs, and answers a question of Griggs,
Kleitman, and Shastri on a lower bound of the leaf number in triangle-free
graphs.
-/

namespace SizeOrderConnectedDomination

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The ≤ direction: for any spanning tree, non-leaf vertices form a
connected dominating set, so `Ls ≤ n - γ_c`. -/
lemma Ls_le_order_minus_connDomNum
    (G : SimpleGraph α) (h : G.Connected) (hn : Fintype.card α ≥ 3) :
    G.Ls ≤ (Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ) := by
  -- Get the optimal spanning tree T achieving Ls
  obtain ⟨T, hSpan, hTree, hLs⟩ :=
    WrittenOnTheWallII.GraphConjecture2.max_leaf_tree_exists G h
  -- Define leaves and internal vertices
  let leaves := T.verts.toFinset.filter (fun v => T.degree v = 1)
  let internal := T.verts.toFinset.filter (fun v => T.degree v ≠ 1)
  -- Partition: leaves ∪ internal = all vertices (= Finset.univ since spanning)
  have hSpanUniv : T.verts.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun v => Set.mem_toFinset.mpr (hSpan v))
  have hPartition : leaves.card + internal.card = Fintype.card α := by
    have h1 : leaves.card + internal.card = T.verts.toFinset.card := by
      show (T.verts.toFinset.filter _).card + (T.verts.toFinset.filter _).card = _
      exact T.verts.toFinset.filter_card_add_filter_neg_card_eq_card _
    rw [h1, hSpanUniv, Finset.card_univ]
  -- Internal vertices form a connected dominating set of G
  -- Dominating: every leaf has a neighbor in internal (via tree edge, using n ≥ 3)
  have hDom : G.IsDominating (internal : Set α) := by
    intro v
    by_cases hv : T.degree v ≠ 1
    · left
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr (hSpan v), hv⟩)
    · right; push_neg at hv
      -- v is a leaf (degree 1): use degree_eq_one_iff_existsUnique_adj to get unique neighbor
      obtain ⟨u, hu, huniq⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hv
      -- T.Adj v u → G.Adj v u (tree edges are graph edges)
      refine ⟨u, ?_, T.adj_sub hu⟩
      -- u ∈ internal: T.degree u ≠ 1
      apply Finset.mem_coe.mpr; apply Finset.mem_filter.mpr
      refine ⟨Set.mem_toFinset.mpr (hSpan u), ?_⟩
      -- If T.degree u = 1, then u's unique neighbor is v
      intro hu1
      obtain ⟨w, hw, hwuniq⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hu1
      -- w must be v (since T.Adj u v by symmetry)
      have hwv : w = v := (hwuniq v (T.symm hu)).symm
      -- So u's only neighbor is v and v's only neighbor is u
      -- The tree T has only {u,v} as connected vertices → contradicts n ≥ 3
      -- Walk induction: any vertex reachable from {v,u} in T is {v,u}
      have hReach : ∀ (a z : T.verts) (w : T.coe.Walk a z),
          (a.val = v ∨ a.val = u) → z.val = v ∨ z.val = u := by
        intro a z w ha
        induction w with
        | nil => exact ha
        | cons hadj _ ih =>
          exact ih (by
            rcases ha with ha | ha
            · exact Or.inr (huniq _ (ha ▸ hadj))
            · exact Or.inl ((hwv ▸ hwuniq _ (ha ▸ hadj))))
      -- So every vertex of T is v or u
      have hAll : ∀ z : T.verts, z.val = v ∨ z.val = u := fun z =>
        hReach _ z (hTree.1.preconnected ⟨v, hSpan v⟩ z).some (Or.inl rfl)
      -- Therefore card T.verts ≤ 2
      have hCard : Fintype.card T.verts ≤ 2 := by
        have hInj : Fintype.card T.verts ≤ Fintype.card Bool := by
          apply Fintype.card_le_of_surjective (fun b => if b then ⟨v, hSpan v⟩ else ⟨u, hSpan u⟩)
          intro ⟨z, hz⟩
          rcases hAll ⟨z, hz⟩ with rfl | rfl
          · exact ⟨true, rfl⟩
          · exact ⟨false, rfl⟩
        simpa using hInj
      have hCard2 : Fintype.card α ≤ 2 := by
        rwa [show Fintype.card T.verts = Fintype.card α from
          Fintype.card_congr (Equiv.subtypeUnivEquiv hSpan)] at hCard
      omega
  -- Connected: internal vertices induce a connected subgraph (removing
  -- leaves from a tree on ≥ 3 vertices keeps it connected, and T ≤ G)
  have hConn : (G.induce (internal : Set α)).Connected := by
    -- Internal is nonempty (from hDom: any leaf has an internal neighbor, and n ≥ 3 means leaves exist)
    have hIntNe : (internal : Set α).Nonempty := by
      -- The tree has ≥ 3 vertices, so it has a leaf v with internal neighbor u
      obtain ⟨v₀, _⟩ : ∃ v₀ : α, True := ⟨Classical.arbitrary α, trivial⟩
      rcases hDom v₀ with h | ⟨u₀, hu₀, _⟩
      · exact ⟨v₀, h⟩
      · exact ⟨u₀, hu₀⟩
    haveI : Nonempty ↥(internal : Set α) := ⟨⟨_, hIntNe.some_mem⟩⟩
    exact Connected.mk (fun ⟨a, ha⟩ ⟨b, hb⟩ => by
      -- a, b are internal (degree ≠ 1 in T)
      have ha_deg : T.degree a ≠ 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb_deg : T.degree b ≠ 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      -- Get walk from a to b in T.coe, convert to path
      obtain ⟨walk⟩ := hTree.1.preconnected ⟨a, hSpan a⟩ ⟨b, hSpan b⟩
      -- T.spanningCoe is preconnected (map T.coe walks via Subtype.val)
      have hTSC_preconn : T.spanningCoe.Preconnected := by
        intro u v
        exact (hTree.1.preconnected ⟨u, hSpan u⟩ ⟨v, hSpan v⟩).map
          ⟨Subtype.val, fun h => h⟩
      -- Every non-internal vertex has subsingleton neighborSet in T.spanningCoe
      have hLeafSub : ∀ v, v ∉ (internal : Set α) →
          (T.spanningCoe.neighborSet v).Subsingleton := by
        intro v hv
        simp only [internal, Finset.mem_coe, Finset.mem_filter, Set.mem_toFinset,
          not_and, not_not] at hv
        have hdeg1 : T.degree v = 1 := hv (hSpan v)
        obtain ⟨w, hw, huniq⟩ := T.degree_eq_one_iff_existsUnique_adj.mp hdeg1
        intro x hx y hy
        exact (huniq x hx).trans (huniq y hy).symm
      -- T.spanningCoe.induce internal is preconnected
      have hIndPC := hTSC_preconn.induce_of_degree_eq_one hLeafSub
      -- T.spanningCoe ≤ G, so T.spanningCoe.induce s ≤ G.induce s
      exact (hIndPC ⟨a, ha⟩ ⟨b, hb⟩).mono
        (SimpleGraph.comap_monotone _ T.spanningCoe_le))
  -- So γ_c ≤ |internal|
  have hGamma : G.connectedDominationNumber ≤ internal.card := by
    apply Nat.sInf_le
    exact ⟨internal, ⟨hDom, hConn⟩, rfl⟩
  -- Conclude: Ls = |leaves| ≤ n - γ_c
  rw [hLs]
  have h1 : (leaves.card : ℝ) + (internal.card : ℝ) = (Fintype.card α : ℝ) := by
    exact_mod_cast hPartition
  have h2 : (G.connectedDominationNumber : ℝ) ≤ (internal.card : ℝ) := by
    exact_mod_cast hGamma
  linarith

/-- The ≥ direction: given a min connected dominating set D, build a
spanning tree with n - |D| leaves, so `Ls ≥ n - γ_c`. -/
lemma Ls_ge_order_minus_connDomNum
    (G : SimpleGraph α) (h : G.Connected) :
    G.Ls ≥ (Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ) := by
  -- Step 1: The set of connected-domination-set sizes is nonempty.
  have hNe : {n | ∃ D : Finset α, G.IsConnectedDominating (D : Set α) ∧
      D.card = n}.Nonempty := by
    refine ⟨Fintype.card α, Finset.univ, ⟨?_, ?_⟩, Finset.card_univ⟩
    · intro v; exact Or.inl (Finset.mem_coe.mpr (Finset.mem_univ v))
    · haveI : Nonempty (↑(Finset.univ : Finset α) : Set α) :=
        ⟨⟨Classical.arbitrary α, Finset.mem_coe.mpr (Finset.mem_univ _)⟩⟩
      refine Connected.mk (fun a b => ?_)
      let lift : G →g G.induce (↑(Finset.univ : Finset α) : Set α) :=
        ⟨fun x => ⟨x, Finset.mem_coe.mpr (Finset.mem_univ x)⟩, fun h => h⟩
      exact (h.preconnected a.val b.val).map lift
  -- Step 2: Get D achieving γ_c via well-ordering of ℕ.
  obtain ⟨D, ⟨hDom, hDConn⟩, hDcard⟩ := Nat.sInf_mem hNe
  -- Step 3: Build a spanning tree with ≥ n - |D| leaves.
  -- 3a: Spanning tree of G[D].
  obtain ⟨T_D, hT_D_le, hT_D_tree⟩ := hDConn.exists_isTree_le
  -- 3b: For each v ∉ D, choose a G-neighbor in D.
  have hNeighbor : ∀ v : α, v ∉ (D : Set α) → ∃ d ∈ (D : Set α), G.Adj v d := by
    intro v hv
    rcases hDom v with hv_in | ⟨d, hd, hadj⟩
    · exact absurd hv_in hv
    · exact ⟨d, hd, hadj⟩
  choose! f hf_mem hf_adj using hNeighbor
  -- 3c: Build T: T_D edges (lifted) plus pendant edges {v, f(v)} for v ∉ D.
  let Ds : Set α := ↑D
  let T : SimpleGraph α :=
    { Adj := fun u v =>
        (∃ (hu : u ∈ Ds) (hv : v ∈ Ds), T_D.Adj ⟨u, hu⟩ ⟨v, hv⟩) ∨
        (u ∉ Ds ∧ v = f u) ∨
        (v ∉ Ds ∧ u = f v)
      symm := fun {u v} huv => by
        rcases huv with ⟨hu, hv, hadj⟩ | ⟨hu, rfl⟩ | ⟨hv, rfl⟩
        · exact Or.inl ⟨hv, hu, T_D.symm hadj⟩
        · exact Or.inr (Or.inr ⟨hu, rfl⟩)
        · exact Or.inr (Or.inl ⟨hv, rfl⟩)
      loopless := fun {v} hv => by
        rcases hv with ⟨hv1, _, hadj⟩ | ⟨hv_notD, hv_eq⟩ | ⟨hv_notD, hv_eq⟩
        · exact T_D.loopless ⟨v, hv1⟩ hadj
        · exact hv_notD (hv_eq ▸ hf_mem v hv_notD)
        · exact hv_notD (hv_eq ▸ hf_mem v hv_notD) }
  -- 3d: T ≤ G.
  have hT_le : T ≤ G := by
    intro u v huv
    rcases huv with ⟨hu, hv, hadj⟩ | ⟨hu, rfl⟩ | ⟨hv, rfl⟩
    · exact hT_D_le hadj
    · exact hf_adj u hu
    · exact (hf_adj v hv).symm
  -- 3e: T is a tree (connected + acyclic).
  -- Connectivity: any vertex reaches D via at most one pendant edge,
  -- then T_D connects within D.
  have hT_conn : T.Connected := by
    haveI : Nonempty α := ⟨Classical.arbitrary α⟩
    refine Connected.mk (fun u v => ?_)
    -- First, show every vertex w is T-reachable from f(w) (if w ∉ D) or from itself (if w ∈ D)
    -- i.e., every vertex reaches some D-vertex in T.
    suffices key : ∀ (a b : α), a ∈ Ds → b ∈ Ds → T.Reachable a b by
      -- If u ∈ D and v ∈ D: use key
      -- If u ∉ D: T.Adj u (f u), then use key for f u, ...
      -- If v ∉ D: ..., then T.Adj (f v) v
      have hu_reach : T.Reachable u (if hu : u ∈ Ds then u else f u) := by
        by_cases hu : u ∈ Ds
        · simp [hu]
        · simp [hu]
          exact (show T.Adj u (f u) from Or.inr (Or.inl ⟨hu, rfl⟩)).reachable
      have hv_reach : T.Reachable (if hv : v ∈ Ds then v else f v) v := by
        by_cases hv : v ∈ Ds
        · simp [hv]
        · simp [hv]
          exact (show T.Adj (f v) v from Or.inr (Or.inr ⟨hv, rfl⟩)).reachable
      have hu_D : (if hu : u ∈ Ds then u else f u) ∈ Ds := by
        split <;> [assumption; exact hf_mem u ‹_›]
      have hv_D : (if hv : v ∈ Ds then v else f v) ∈ Ds := by
        split <;> [assumption; exact hf_mem v ‹_›]
      exact hu_reach.trans ((key _ _ hu_D hv_D).trans hv_reach)
    -- Show D-vertices are T-reachable via T_D edges (which are T edges).
    intro a b ha hb
    have hT_D_reach := hT_D_tree.1.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    exact hT_D_reach.map ⟨Subtype.val, fun {x y} hadj =>
      Or.inl ⟨x.prop, y.prop, hadj⟩⟩
  -- Acyclicity: any closed trail in T must be nil.
  -- A non-D vertex v has exactly one T-neighbor (f v), so a trail can't
  -- pass through v (it would need the edge {v, f v} twice).
  -- A trail using only D-vertices uses only T_D-edges, but T_D is acyclic.
  -- Every non-D vertex v has exactly one T-neighbor (f v).
  have hT_adj_nonD : ∀ v, v ∉ Ds → ∀ w, T.Adj v w → w = f v := by
    intro v hv w hadj
    rcases hadj with ⟨hv_D, _, _⟩ | ⟨_, hw⟩ | ⟨hw_notD, hv_eq⟩
    · exact absurd hv_D hv
    · exact hw
    · exact absurd (hv_eq ▸ hf_mem w hw_notD) hv
  -- Prove T is a tree using connected + acyclic.
  -- Acyclicity: any closed trail in T must be nil.
  -- T is a tree. Proof strategy: T is connected (shown above) and we
  -- show it has exactly n - 1 edges using isTree_iff_connected_and_card.
  -- Alternatively, we show T.IsAcyclic by projecting cycles to T_D.
  --
  -- We prove T.IsAcyclic. The key fact (hT_adj_nonD): every non-D vertex
  -- v has exactly one T-neighbor, namely f v.
  -- Any closed trail in T through a non-D vertex v must use the edge
  -- {v, f v} at least twice (to enter and leave v), contradiction.
  -- A closed trail using only D-vertices projects to T_D, contradicting
  -- T_D being acyclic.
  -- T.Adj between two D-vertices must come from a T_D edge
  have hT_adj_D : ∀ {u v : α} (hu : u ∈ Ds) (hv : v ∈ Ds),
      T.Adj u v → T_D.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v hu hv hadj
    rcases hadj with ⟨_, _, hadj'⟩ | ⟨hu', _⟩ | ⟨hv', _⟩
    · exact hadj'
    · exact absurd hu hu'
    · exact absurd hv hv'
  -- T.induce Ds ≤ T_D (edges between D-vertices in T come from T_D)
  have hT_induce_le_TD : T.induce Ds ≤ T_D := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ hadj
    exact hT_adj_D hu hv hadj
  have hT_acyc : T.IsAcyclic := by
    intro v c hc
    -- Case split: is there a non-D vertex on the cycle?
    by_cases hall : ∀ w, w ∈ c.support → w ∈ Ds
    · -- All vertices in D: induce the cycle into T.induce Ds, then
      -- map to T_D and contradict T_D acyclicity.
      -- Step 1: induce c into (T.induce Ds)
      let c_ind := c.induce Ds hall
      -- Step 2: c_ind is a cycle (Walk.induce followed by Walk.map gives c back)
      have hc_ind : c_ind.IsCycle := by
        have h : c_ind.map (Embedding.induce Ds).toHom = c := Walk.map_induce c hall
        rw [← h] at hc
        exact (Walk.map_isCycle_iff_of_injective (Embedding.induce (G := T) Ds).injective).mp hc
      -- Step 3: map to T_D using hT_induce_le_TD, preserving the cycle
      exact hT_D_tree.2 (c_ind.mapLe hT_induce_le_TD)
        (hc_ind.mapLe hT_induce_le_TD)
    · -- Some non-D vertex w exists on the cycle
      push_neg at hall
      obtain ⟨w, hw_mem, hw_notD⟩ := hall
      -- Rotate the cycle to start at w
      have hc' := hc.rotate hw_mem
      -- c'.snd is the first neighbor of w, which must be f w
      have h_snd : (c.rotate hw_mem).snd = f w :=
        hT_adj_nonD w hw_notD _ (Walk.adj_snd hc'.not_nil)
      -- c'.penultimate is the last vertex before w, also must be f w
      have h_pen : (c.rotate hw_mem).penultimate = f w :=
        hT_adj_nonD w hw_notD _ (T.symm (Walk.adj_penultimate hc'.not_nil))
      -- But snd ≠ penultimate in a cycle
      exact hc'.snd_ne_penultimate (h_snd.trans h_pen.symm)
  have hT_tree : T.IsTree := by
    rw [SimpleGraph.isTree_iff]
    exact ⟨hT_conn, hT_acyc⟩
  -- Step 4: Every v ∉ D has T.degree v = 1 (it is a leaf).
  -- So #leaves ≥ |Dᶜ| = n - |D|.
  have hT_leaves : (Finset.univ.filter (fun v => T.degree v = 1)).card ≥
      Fintype.card α - D.card := by
    -- Every v ∉ D has exactly one T-neighbor (namely f v), so T.degree v = 1.
    -- Therefore Dᶜ ⊆ {v | T.degree v = 1}, giving the bound.
    have hDeg1 : ∀ v, v ∉ Ds → T.degree v = 1 := by
      intro v hv
      -- T.neighborFinset v = {f v} when v ∉ D
      -- The only T-neighbor of v is f v:
      -- T.Adj v w ↔ (w = f v) when v ∉ D
      have hAdj_iff : ∀ w, T.Adj v w ↔ w = f v := by
        intro w
        constructor
        · intro hadj
          rcases hadj with ⟨hv_D, _, _⟩ | ⟨_, hw⟩ | ⟨hw_notD, hv_eq⟩
          · exact absurd hv_D hv
          · exact hw
          · -- w ∉ D and v = f w, but f w ∈ D and v ∉ D, contradiction
            exact absurd (hv_eq ▸ hf_mem w hw_notD) hv
        · intro hw
          exact Or.inr (Or.inl ⟨hv, hw⟩)
      -- T.neighborFinset v = {f v}
      have : T.neighborFinset v = {f v} := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
        exact hAdj_iff w
      rw [SimpleGraph.degree, this, Finset.card_singleton]
    -- Now show Dᶜ ⊆ leaves
    suffices h_sub : Dᶜ ⊆ Finset.univ.filter (fun v => T.degree v = 1) by
      calc (Finset.univ.filter (fun v => T.degree v = 1)).card
          ≥ Dᶜ.card := Finset.card_le_card h_sub
        _ = Fintype.card α - D.card := by
            rw [Finset.card_compl]
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hDeg1 v (by simpa [Ds, Finset.mem_coe] using Finset.mem_compl.mp hv)
  -- Combine: Ls ≥ #leaves ≥ n - |D| = n - γ_c.
  -- Inline the argument from leaf_number_ge_subtree_leaves.
  let T_sub := SimpleGraph.toSubgraph T hT_le
  have hSpanning : T_sub.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hT_le
  have hTsubTree : T_sub.coe.IsTree := by
    let lift : T →g T_sub.coe := ⟨fun a => ⟨a, Set.mem_univ a⟩, fun h => h⟩
    let proj : T_sub.coe →g T := ⟨Subtype.val, fun h => h⟩
    haveI : Nonempty T_sub.verts := ⟨⟨Classical.arbitrary α, Set.mem_univ _⟩⟩
    exact ⟨Connected.mk (fun ⟨u, _⟩ ⟨v, _⟩ =>
      (hT_tree.1.preconnected u v).map lift),
      fun ⟨v, _⟩ c hc => hT_tree.2 (c.map proj)
        (hc.map Subtype.val_injective)⟩
  let fL := (fun S : G.Subgraph =>
    (((S.verts.toFinset.filter (fun v => S.degree v = 1)).card) : ℝ))
  let S_set := {S : G.Subgraph | S.IsSpanning ∧ S.coe.IsTree}
  have h_bdd : BddAbove (fL '' S_set) :=
    (Set.Finite.image fL (Set.toFinite S_set)).bddAbove
  have h_mem : T_sub ∈ S_set := ⟨hSpanning, hTsubTree⟩
  have h_Ls_ge : fL T_sub ≤ G.Ls := le_csSup h_bdd (Set.mem_image_of_mem fL h_mem)
  -- fL T_sub = leaf count of T
  have h_deg : ∀ v, T_sub.degree v = T.degree v := by
    intro v
    rw [SimpleGraph.Subgraph.degree, SimpleGraph.degree, ← Set.toFinset_card]
    congr 1; ext w
    simp only [Set.mem_toFinset, SimpleGraph.Subgraph.neighborSet,
      SimpleGraph.mem_neighborFinset, T_sub, SimpleGraph.toSubgraph, Set.mem_setOf_eq]
  have h_verts : T_sub.verts.toFinset = Finset.univ := by
    ext v; simp [T_sub, SimpleGraph.toSubgraph]
  have h_fL_eq : fL T_sub = ((Finset.univ.filter (fun v => T.degree v = 1)).card : ℝ) := by
    show ((T_sub.verts.toFinset.filter (fun v => T_sub.degree v = 1)).card : ℝ) = _
    rw [h_verts]; norm_cast; congr 1
    exact Finset.filter_congr (fun v _ => by rw [h_deg v])
  have hDcard' : (D.card : ℝ) = (G.connectedDominationNumber : ℝ) := by
    exact_mod_cast hDcard
  have h_nat_sub : ((Fintype.card α - D.card : ℕ) : ℝ) ≥
      (Fintype.card α : ℝ) - (D.card : ℝ) := by
    simp [Nat.cast_sub (Finset.card_le_univ D)]
  calc G.Ls ≥ fL T_sub := h_Ls_ge
    _ = ↑(Finset.univ.filter (fun v => T.degree v = 1)).card := h_fL_eq
    _ ≥ ↑(Fintype.card α - D.card) := by exact_mod_cast hT_leaves
    _ ≥ (Fintype.card α : ℝ) - (D.card : ℝ) := h_nat_sub
    _ = (Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ) := by rw [hDcard']

/-- Equation (1.1): `Ls(G) = n - γ_c(G)` for connected graphs with `n ≥ 3`.
Fails for K₂ where Ls = 2 but n - γ_c = 1. -/
@[category research open, AMS 5]
theorem leaf_number_eq_order_minus_connected_domination
    (G : SimpleGraph α) (h : G.Connected) (hn : Fintype.card α ≥ 3) :
    G.Ls = (Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ) :=
  le_antisymm (Ls_le_order_minus_connDomNum G h hn)
    (Ls_ge_order_minus_connDomNum G h)

/-- Lemma 1.2: If `T'` is a subtree of a connected graph `G`, then `L(G) ≥ L(T')`.

More precisely, the leaf number of `G` is at least the number of leaves of any
tree that is a subgraph of `G`. -/
@[category research solved, AMS 5]
theorem leaf_number_ge_subtree_leaves
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT_le : T ≤ G) (hT_tree : T.IsTree) :
    G.Ls ≥ (Finset.univ.filter (fun v => T.degree v = 1)).card := by
  -- Convert T to a Subgraph of G
  let T_sub := SimpleGraph.toSubgraph T hT_le
  have hSpanning : T_sub.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hT_le
  -- Homomorphisms between T and T_sub.coe (same edges, different types)
  let lift : T →g T_sub.coe := ⟨fun a => ⟨a, Set.mem_univ a⟩, fun h => h⟩
  let proj : T_sub.coe →g T := ⟨Subtype.val, fun h => h⟩
  -- T_sub.coe is a tree
  have hTree : T_sub.coe.IsTree := by
    haveI : Nonempty T_sub.verts := ⟨⟨Classical.arbitrary α, Set.mem_univ _⟩⟩
    exact ⟨Connected.mk (fun ⟨u, _⟩ ⟨v, _⟩ => (hT_tree.1.preconnected u v).map lift),
           fun ⟨v, _⟩ c hc => hT_tree.2 (c.map proj) (hc.map Subtype.val_injective)⟩
  -- Use the same setup as max_leaf_tree_exists
  let f := (fun S : G.Subgraph =>
    (((S.verts.toFinset.filter (fun v => S.degree v = 1)).card) : ℝ))
  let S_set := {S : G.Subgraph | S.IsSpanning ∧ S.coe.IsTree}
  have h_Ls_eq : G.Ls = sSup (f '' S_set) := rfl
  have h_bdd : BddAbove (f '' S_set) :=
    (Set.Finite.image f (Set.toFinite S_set)).bddAbove
  have h_mem : T_sub ∈ S_set := ⟨hSpanning, hTree⟩
  have h_le : f T_sub ≤ G.Ls := by
    rw [h_Ls_eq]
    exact le_csSup h_bdd (Set.mem_image_of_mem f h_mem)
  -- f T_sub = leaf count of T (degrees and vertex sets match)
  suffices h_eq : f T_sub = ((Finset.univ.filter (fun v => T.degree v = 1)).card : ℝ) by
    linarith
  -- T_sub.verts.toFinset = Finset.univ and T_sub.degree = T.degree
  show ((T_sub.verts.toFinset.filter (fun v => T_sub.degree v = 1)).card : ℝ) = _
  -- Degrees match: T_sub.degree v = T.degree v
  have h_deg : ∀ v, T_sub.degree v = T.degree v := by
    intro v
    -- Subgraph.degree = Fintype.card (neighborSet v)
    -- SimpleGraph.degree = (neighborFinset v).card = (neighborSet v).toFinset.card
    rw [SimpleGraph.Subgraph.degree, SimpleGraph.degree, ← Set.toFinset_card]
    congr 1; ext w
    simp only [Set.mem_toFinset, SimpleGraph.Subgraph.neighborSet,
      SimpleGraph.mem_neighborFinset, T_sub, SimpleGraph.toSubgraph, Set.mem_setOf_eq]
  have h_verts : T_sub.verts.toFinset = Finset.univ := by
    ext v; simp [T_sub, SimpleGraph.toSubgraph]
  rw [h_verts]; norm_cast; congr 1
  exact Finset.filter_congr (fun v _ => by rw [h_deg v])

/-- In a triangle-free graph, the neighborhoods of adjacent vertices are disjoint.
Therefore `|N(x) ∪ N(y)| = deg(x) + deg(y)` for any edge xy. -/
lemma neighborFinset_disjoint_of_adj_triangleFree
    (G : SimpleGraph α) [DecidableRel G.Adj] (hTF : G.CliqueFree 3)
    (x y : α) (hxy : G.Adj x y) :
    Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
  rw [Finset.disjoint_left]
  intro w hw_x hw_y
  rw [SimpleGraph.mem_neighborFinset] at hw_x hw_y
  -- w is adjacent to both x and y. Since neighborhoods are independent sets
  -- in triangle-free graphs, w ∈ N(x) and w ∈ N(y) means x and y are both
  -- in N(w), and G.Adj x y contradicts independence of N(w).
  exact G.isIndepSet_neighborSet_of_triangleFree hTF w
    (G.symm hw_x) (G.symm hw_y) (G.ne_of_adj hxy) hxy

/-- In a triangle-free connected graph, for any edge xy:
`deg(x) + deg(y) ≤ Ls + 2`.

This follows from `union_neighbor_bound` (which gives `|N(x) ∪ N(y)| ≤ Ls + 2`)
and the fact that triangle-free makes N(x) and N(y) disjoint. -/
lemma degree_sum_le_Ls_plus_2_of_triangleFree
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hTF : G.CliqueFree 3) (x y : α) (hxy : G.Adj x y) :
    (G.degree x : ℝ) + (G.degree y : ℝ) ≤ G.Ls + 2 := by
  have h_disj := neighborFinset_disjoint_of_adj_triangleFree G hTF x y hxy
  have h_union := WrittenOnTheWallII.GraphConjecture2.union_neighbor_bound G h x y hxy
  have h_card : (G.neighborFinset x ∪ G.neighborFinset y).card =
      (G.neighborFinset x).card + (G.neighborFinset y).card := by
    exact Finset.card_union_of_disjoint h_disj
  rw [h_card] at h_union
  simp only [SimpleGraph.degree] at h_union ⊢
  exact_mod_cast h_union

/-- Key edge-sum bound: `∑_v deg(v)² ≤ m · (Ls + 2)` for triangle-free
connected graphs.

This follows from the handshaking-like identity `∑_{uv ∈ E} (deg u + deg v) = ∑_v deg(v)²`
and `deg(u) + deg(v) ≤ Ls + 2` for each edge. -/
lemma sum_degree_sq_le_of_triangleFree
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hTF : G.CliqueFree 3) :
    (∑ v, (G.degree v : ℝ) ^ 2) ≤
      (G.edgeFinset.card : ℝ) * (G.Ls + 2) := by
  classical
  -- Key identity: ∑_v deg(v)² = ∑_{d : Dart} deg(d.fst)
  -- Proof via Dart ≃ Σ v, neighborSet v.
  have h_sq_eq_dart : (∑ v, (G.degree v : ℝ) ^ 2) =
      ∑ d : G.Dart, (G.degree d.fst : ℝ) := by
    -- Use the fiber decomposition of Darts by d.fst.
    -- ∑_d deg(d.fst) = ∑_v ∑_{d | d.fst = v} deg(d.fst) = ∑_v |fiber_v| * deg(v)
    --               = ∑_v deg(v) * deg(v) = ∑_v deg(v)²
    symm
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := fun d : G.Dart => d.fst)
      (fun _ _ => Finset.mem_univ _) (fun d => (G.degree d.fst : ℝ))]
    congr 1; ext v
    -- In the fiber {d | d.fst = v}, deg(d.fst) = deg(v) for all d.
    rw [show ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      (G.degree d.fst : ℝ) = ∑ _d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      (G.degree v : ℝ) from
        Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.mp hd).2])]
    rw [Finset.sum_const, nsmul_eq_mul, sq]
    congr 1
    exact_mod_cast G.dart_fst_fiber_card_eq_degree v
  -- ∑_d deg(d.fst) = ∑_d deg(d.snd) via the involution d ↦ d.symm
  have h_symm : ∑ d : G.Dart, (G.degree d.fst : ℝ) =
      ∑ d : G.Dart, (G.degree d.snd : ℝ) :=
    Fintype.sum_equiv (SimpleGraph.Dart.symm_involutive.toPerm)
      _ _ (fun d => by simp [SimpleGraph.Dart.symm])
  -- 2 * ∑_d deg(d.fst) = ∑_d (deg(d.fst) + deg(d.snd))
  have h_two_sum : 2 * ∑ d : G.Dart, (G.degree d.fst : ℝ) =
      ∑ d : G.Dart, ((G.degree d.fst : ℝ) + (G.degree d.snd : ℝ)) := by
    have := @Finset.sum_add_distrib G.Dart ℝ Finset.univ Real.instAddCommMonoid
      (fun d => (G.degree d.fst : ℝ)) (fun d => (G.degree d.snd : ℝ))
    linarith
  -- For each dart d, deg(d.fst) + deg(d.snd) ≤ Ls + 2
  have h_dart_bound : ∀ d : G.Dart,
      (G.degree d.fst : ℝ) + (G.degree d.snd : ℝ) ≤ G.Ls + 2 :=
    fun d => degree_sum_le_Ls_plus_2_of_triangleFree G h hTF d.fst d.snd d.adj
  -- |Darts| = 2 * |E|
  have h_dart_card : Fintype.card G.Dart = 2 * G.edgeFinset.card :=
    G.dart_card_eq_twice_card_edges
  -- Combine everything
  rw [h_sq_eq_dart]
  have key : 2 * ∑ d : G.Dart, (G.degree d.fst : ℝ) ≤
      2 * (G.edgeFinset.card : ℝ) * (G.Ls + 2) := by
    rw [h_two_sum]
    have h1 : ∑ d : G.Dart, ((G.degree d.fst : ℝ) + (G.degree d.snd : ℝ)) ≤
        ∑ _d : G.Dart, (G.Ls + 2) :=
      Finset.sum_le_sum (fun d _ => h_dart_bound d)
    have h2 : (∑ _d : G.Dart, (G.Ls + 2)) =
        (Fintype.card G.Dart : ℝ) * (G.Ls + 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : (Fintype.card G.Dart : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast h_dart_card
    calc ∑ d : G.Dart, ((G.degree d.fst : ℝ) + (G.degree d.snd : ℝ))
        ≤ ∑ _d : G.Dart, (G.Ls + 2) := h1
      _ = (Fintype.card G.Dart : ℝ) * (G.Ls + 2) := h2
      _ = 2 * (G.edgeFinset.card : ℝ) * (G.Ls + 2) := by rw [h3]
  linarith

/-- The paper's main bound expressed in terms of Ls:
`m ≤ Ls²/4 + n - 1`.

**WARNING: This statement appears to be false.**

The 3-dimensional hypercube graph Q₃ is a counterexample:
- Q₃ is 3-regular, bipartite (hence triangle-free), and connected.
- n = 8 vertices, m = 12 edges.
- γ_c(Q₃) = 4 (minimum connected dominating set has 4 vertices).
- Ls = n - γ_c = 4 (verified: the best spanning tree has exactly 4 leaves).
- The bound gives m ≤ 4²/4 + 8 - 1 = 4 + 7 = 11.
- But m = 12 > 11.

The paper (Mukwembi, Canad. Math. Bull. 57(1), 2014) proves Theorem 2.1 by
contradiction with a minimum counterexample argument. The proof contains a gap:
it assumes the existence of an edge uv such that G' = G - {u,v} satisfies
γ_c(G) ≤ γ_c(G'), but this need not hold. For Q₃, removing any pair of adjacent
vertices yields G' with γ_c(G') = 2 < 4 = γ_c(Q₃), violating the assumption.

The downstream theorem `size_bound_triangle_free` (which states the bound in
terms of γ_c directly) inherits this issue through the identity Ls = n - γ_c. -/
lemma size_le_Ls_sq_div_4_plus_order_minus_1
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hTF : G.CliqueFree 3) :
    (G.edgeFinset.card : ℝ) ≤ G.Ls ^ 2 / 4 + (Fintype.card α : ℝ) - 1 := by
  -- This statement is false: Q₃ (the 3-cube) is a counterexample.
  -- See the docstring above for details.
  sorry

/-- Theorem 2.1: Let `G` be a connected triangle-free graph of order `n`,
size `m` and connected domination number `gamma_c`. Then
`m <= (n - gamma_c)^2 / 4 + n - 1`, and this bound is tight.

The proof reduces to two key ingredients:
1. Equation (1.1): `Ls = n - gamma_c` (`leaf_number_eq_order_minus_connected_domination`),
   which converts the bound to `m <= Ls^2/4 + n - 1`.
2. The main bound `m <= Ls^2/4 + n - 1` (`size_le_Ls_sq_div_4_plus_order_minus_1`),
   proved in the paper via strong induction on n with vertex removal.

For n = 2, the bound holds trivially since K_2 has m = 1 and the RHS >= 1. -/
@[category research open, AMS 5]
theorem size_bound_triangle_free
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hTF : G.CliqueFree 3) :
    (G.edgeFinset.card : ℝ) ≤
      ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
      + (Fintype.card α : ℝ) - 1 := by
  -- The proof uses Eq (1.1): Ls = n - gamma_c, and the bound m <= Ls^2/4 + n - 1.
  by_cases hn : Fintype.card α ≥ 3
  · -- For n ≥ 3, use Ls = n - γ_c
    have h_eq := leaf_number_eq_order_minus_connected_domination G h hn
    rw [← h_eq]
    exact size_le_Ls_sq_div_4_plus_order_minus_1 G h hTF
  · -- For n < 3: since G is connected and nontrivial, n = 2 and G = K₂
    push_neg at hn
    have hn2 : Fintype.card α = 2 := by
      have h1 : Fintype.card α ≥ 2 := by
        have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial α)
        omega
      omega
    -- K₂ has 1 edge, γ_c = 1
    -- (2 - γ_c)² / 4 + 2 - 1 ≥ 0 + 1 = 1 ≥ m = 1
    -- Actually need to compute: m ≤ (2 - γ_c)²/4 + 1
    -- Since γ_c ≤ n = 2 and γ_c ≥ 1 (for connected), (2 - γ_c)²/4 ≥ 0
    -- And m ≤ n - 1 = 1 for triangle-free on 2 vertices (only K₂)
    -- So m = 1 ≤ (2 - γ_c)²/4 + 1. True since (2 - γ_c)²/4 ≥ 0.
    have hm : G.edgeFinset.card ≤ 1 := by
      have hcard : Fintype.card α = 2 := hn2
      -- In a graph on 2 vertices, there is at most 1 edge
      have : G.edgeFinset.card ≤ (Fintype.card α).choose 2 :=
        G.card_edgeFinset_le_card_choose_two
      simp [hn2] at this
      exact this
    have hγ_nonneg : (0 : ℝ) ≤ ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4 := by
      positivity
    have hm_real : (G.edgeFinset.card : ℝ) ≤ 1 := by exact_mod_cast hm
    have hn2_real : (Fintype.card α : ℝ) = 2 := by exact_mod_cast hn2
    linarith

/-- In a triangle-free graph, the neighborhood of every vertex is independent,
so `α(v) = deg(v)`. -/
lemma indepNeighborsCard_eq_degree_of_triangleFree
    (G : SimpleGraph α) (hTF : G.CliqueFree 3) (v : α) :
    G.indepNeighborsCard v = G.degree v := by
  unfold indepNeighborsCard
  set H := G.induce (G.neighborSet v)
  -- H has no edges: triangle-free means the neighborhood is independent
  have hNoEdge : ∀ (u w : {x // x ∈ G.neighborSet v}), ¬H.Adj u w := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hadj
    exact (G.isIndepSet_neighborSet_of_triangleFree hTF v) ha hb (G.ne_of_adj hadj) hadj
  -- Finset.univ is an independent set in H
  have hUnivIndep : H.IsIndepSet ↑(Finset.univ : Finset {x // x ∈ G.neighborSet v}) := by
    intro a _ b _ _
    exact hNoEdge a b
  -- So indepNum H ≥ Fintype.card
  have hLE : Fintype.card {x // x ∈ G.neighborSet v} ≤ H.indepNum := by
    rw [← Finset.card_univ]
    exact hUnivIndep.card_le_indepNum
  -- And indepNum H ≤ Fintype.card (any finset has card ≤ card of type)
  have hGE : H.indepNum ≤ Fintype.card {x // x ∈ G.neighborSet v} := by
    obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    rw [← hs.2]
    exact Finset.card_le_univ s
  -- Hence indepNum = Fintype.card = degree
  have hCard : Fintype.card {x // x ∈ G.neighborSet v} = G.degree v := by
    rw [← Set.toFinset_card]
    rfl
  omega

/-- In a triangle-free graph, the average local independence equals twice the
edge density: `α̅(G) = 2m/n`. -/
lemma averageIndepNeighbors_eq_of_triangleFree
    (G : SimpleGraph α) (hTF : G.CliqueFree 3) :
    G.averageIndepNeighbors =
      2 * (G.edgeFinset.card : ℝ) / (Fintype.card α : ℝ) := by
  simp only [averageIndepNeighbors, indepNeighbors]
  congr 1
  have h_eq : ∀ v, (G.indepNeighborsCard v : ℝ) = (G.degree v : ℝ) := by
    intro v
    exact_mod_cast indepNeighborsCard_eq_degree_of_triangleFree G hTF v
  conv_lhs => arg 2; ext v; rw [h_eq v]
  have h_hand := G.sum_degrees_eq_twice_card_edges
  exact_mod_cast h_hand

/-- Corollary 2.2: Conjecture 1.1 (Graffiti) for triangle-free graphs.
For a connected triangle-free graph `G`, `L(G) ≥ 2(α̅(G) - 1)`.

This is the triangle-free special case of the conjecture proved in full
generality in `WrittenOnTheWallII.GraphConjecture2.conjecture2`. -/
@[category research solved, AMS 5]
theorem graffiti_conjecture_triangle_free
    (G : SimpleGraph α) (h : G.Connected)
    (hTF : G.CliqueFree 3) :
    2 * (G.l - 1) ≤ G.Ls :=
  WrittenOnTheWallII.GraphConjecture2.conjecture2 G h

/-- Corollary 2.3: For a connected triangle-free graph of order `n` and
size `m`, `L(G) ≥ 4m/n - 2`.

This confirms the speculation of Griggs, Kleitman, and Shastri [4] that
triangle-free graphs contain significantly more leaves. -/
@[category research solved, AMS 5]
theorem leaf_bound_triangle_free_size
    (G : SimpleGraph α) (h : G.Connected)
    (hTF : G.CliqueFree 3)
    (hn : (Fintype.card α : ℝ) ≠ 0) :
    G.Ls ≥ 4 * (G.edgeFinset.card : ℝ) / (Fintype.card α : ℝ) - 2 := by
  have h_l : G.l = 2 * (G.edgeFinset.card : ℝ) / (Fintype.card α : ℝ) := by
    show G.averageIndepNeighbors = _
    exact averageIndepNeighbors_eq_of_triangleFree G hTF
  calc G.Ls ≥ 2 * (G.l - 1) := graffiti_conjecture_triangle_free G h hTF
    _ = 2 * (2 * ↑(G.edgeFinset.card) / ↑(Fintype.card α) - 1) := by rw [h_l]
    _ = 4 * ↑(G.edgeFinset.card) / ↑(Fintype.card α) - 2 := by ring

end SizeOrderConnectedDomination
