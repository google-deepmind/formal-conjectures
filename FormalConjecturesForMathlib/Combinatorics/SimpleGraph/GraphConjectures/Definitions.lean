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
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace SimpleGraph

open Classical Finset List

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `Ls G` is the maximum number of leaves over all spanning trees of `G`.
It is defined to be `0` when `G` is not connected. -/
noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

/-- `n G` is the number of vertices of `G` as a real number. -/
noncomputable def n (_ : SimpleGraph α) : ℝ := Fintype.card α

/-- `m G` is the size of a maximum matching of `G`. -/
noncomputable def m (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => (M.edgeSet.toFinset.card : ℝ)) matchings)

/-- The maximum cardinality among all independent sets `s`
    that maximize the quantity `|s| - |N(s)|`, where `N(s)`
    is the neighborhood of the set `s`. -/
noncomputable def aprime (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  letI indep_sets : Finset (Finset α) := univ.powerset.filter (fun s => G.IsIndepSet (s : Set α))
  letI diff (s : Finset α) : ℤ := (s.card : ℤ) - (⋃ v ∈ (s : Set α), G.neighborSet v).toFinset.card
  letI max_diff := (indep_sets.image diff).max
  letI critical_sets := indep_sets.filter (fun s ↦ diff s = max_diff.getD 0)
  letI max_card := (critical_sets.image Finset.card).max
  (max_card.getD 0 : ℝ)

/-- `largestInducedForestSize G` is the size of a largest induced forest of `G`. -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/--
The maximum number of occurrences of any term of the degree sequence of `G`.
-/
noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`.
Returned as a real number. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

def isIndepSet {β : Type*} [Fintype β] [DecidableEq β] (G : SimpleGraph β) [DecidableRel G.Adj] (s : Finset β) : Bool :=
  let violations := s.filter (fun u =>
    let bad_neighbors := s.filter (fun v => u ≠ v ∧ G.Adj u v)
    bad_neighbors.card > 0
  )
  violations.card = 0

def computableIndepNumOnSubset {β : Type*} [Fintype β] [DecidableEq β] (G : SimpleGraph β) [DecidableRel G.Adj] (V_subset : Finset β) : ℕ :=
  let subsets := V_subset.powerset
  let indep_subsets := subsets.filter (fun s => isIndepSet G s)
  let sizes := indep_subsets.image (fun s => s.card)
  (sizes.max).getD 0

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

def computableIndepNeighborsCard (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  computableIndepNumOnSubset G (G.neighborSet v).toFinset

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Average of `indepNeighbors` over all vertices. -/
noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

def computableAverageIndepNeighbors (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  (∑ v ∈ Finset.univ, (computableIndepNeighborsCard G v : ℚ)) / (Fintype.card α : ℚ)

lemma isIndepSet_induce_iff {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) {S : Set α} {s : Finset {x // x ∈ S}} :
    (G.induce S).IsIndepSet ↑s ↔ SimpleGraph.IsIndepSet G ↑(s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset α) := by
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]

lemma isIndepSet_eq_true_iff (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset α) :
    isIndepSet G s = true ↔ SimpleGraph.IsIndepSet G ↑s := by
  unfold isIndepSet
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]

theorem indepNeighborsCard_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    indepNeighborsCard G v = computableIndepNeighborsCard G v := by
  apply Nat.le_antisymm
  · unfold indepNeighborsCard
    unfold indepNum
    apply csSup_le
    · use 0
      simp only [Set.mem_setOf_eq]
      use ∅
      rw [SimpleGraph.isNIndepSet_iff]
      simp
    · intro n hn
      rcases hn with ⟨s', hs⟩
      rw [SimpleGraph.isNIndepSet_iff] at hs
      rcases hs with ⟨hs_indep, hs_card⟩
      set subsets := (G.neighborSet v).toFinset.powerset
      set indep_subsets := subsets.filter (fun s => isIndepSet G s)
      set sizes := indep_subsets.image (fun s => s.card)
      unfold computableIndepNeighborsCard
      change n ≤ Option.getD sizes.max 0

      let T := s'.map ⟨Subtype.val, Subtype.val_injective⟩
      have hT_card : T.card = n := by
        simp [T, hs_card]
      have hT_subset : T ⊆ (G.neighborSet v).toFinset := by
        intro x hx
        rw [Finset.mem_map] at hx
        rcases hx with ⟨y, hy, rfl⟩
        simp [y.property]
      have hT_indep : isIndepSet G T = true := by
        rw [isIndepSet_eq_true_iff]
        rw [← isIndepSet_induce_iff]
        exact hs_indep
      have hT_mem_sizes : n ∈ sizes := by
        rw [Finset.mem_image]
        use T
        refine ⟨?_, hT_card⟩
        rw [Finset.mem_filter]
        refine ⟨?_, hT_indep⟩
        rw [Finset.mem_powerset]
        exact hT_subset

      rcases h_max : sizes.max with _ | m
      · exfalso
        have h_empty : sizes = ∅ := by
          rw [← Finset.max_eq_bot]
          exact h_max
        rw [h_empty] at hT_mem_sizes
        simp at hT_mem_sizes
      · simp
        exact Finset.le_max_of_eq hT_mem_sizes h_max
  · -- RHS ≤ LHS
    set subsets := (G.neighborSet v).toFinset.powerset
    set indep_subsets := subsets.filter (fun s => isIndepSet G s)
    set sizes := indep_subsets.image (fun s => s.card)
    unfold computableIndepNeighborsCard
    change Option.getD sizes.max 0 ≤ indepNeighborsCard G v

    rcases h_max : sizes.max with _ | m
    · simp
    · simp
      have hm : m ∈ sizes := Finset.mem_of_max h_max
      rw [Finset.mem_image] at hm
      rcases hm with ⟨T, hT, rfl⟩
      rw [Finset.mem_filter] at hT
      rcases hT with ⟨hT_sub, hT_indep_bool⟩
      rw [isIndepSet_eq_true_iff] at hT_indep_bool

      have hT_sub_subset : T ⊆ (G.neighborSet v).toFinset := by
        rw [← Finset.mem_powerset]
        exact hT_sub

      set s' : Finset {x // x ∈ G.neighborSet v} := T.attach.map ⟨fun x => ⟨x.1, by
        have h := hT_sub_subset x.2
        simp at h
        exact h⟩, fun x y h_eq => by
        injection h_eq with h1
        exact Subtype.ext h1⟩

      have hs'_card : s'.card = T.card := by
        rw [Finset.card_map, Finset.card_attach]

      have hs'_indep : (G.induce (G.neighborSet v)).IsIndepSet s' := by
        rw [@isIndepSet_induce_iff α _ _ G]
        have h_map_eq : (s'.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset α) = T := by
          rw [Finset.map_map]
          have h_fun_eq : ((⟨fun x => ⟨x.1, by
            have h := hT_sub_subset x.2
            simp at h
            exact h⟩, fun x y h_eq => by
            injection h_eq with h1
            exact Subtype.ext h1⟩ : {x // x ∈ T} ↪ {y // y ∈ G.neighborSet v}).trans ⟨Subtype.val, Subtype.val_injective⟩ : {x // x ∈ T} ↪ α) = ⟨Subtype.val, Subtype.val_injective⟩ := by
            ext x
            rfl
          rw [h_fun_eq]
          exact Finset.attach_map_val
        rw [h_map_eq]
        exact hT_indep_bool

      have h_le := SimpleGraph.IsIndepSet.card_le_indepNum hs'_indep
      rw [hs'_card] at h_le
      exact h_le

theorem averageIndepNeighbors_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    averageIndepNeighbors G = (computableAverageIndepNeighbors G : ℝ) := by
  unfold averageIndepNeighbors indepNeighbors computableAverageIndepNeighbors
  norm_cast
  simp [indepNeighborsCard_eq_computable]

def reachableStep (G : SimpleGraph α) [DecidableRel G.Adj] (E_sub : Finset (Sym2 α)) (S : Finset α) : Finset α :=
  S ∪ (S.biUnion (fun v =>
    Finset.univ.filter (fun u => Sym2.mk (v, u) ∈ E_sub)
  ))

def isConnectedSubgraph (G : SimpleGraph α) [DecidableRel G.Adj] (E_sub : Finset (Sym2 α)) (v0 : α) : Bool :=
  let n := Fintype.card α
  let reachable_final := (Nat.iterate (reachableStep G E_sub) n) {v0}
  reachable_final.card = n

def edgeSubsetsOfSize (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : Finset (Finset (Sym2 α)) :=
  G.edgeFinset.powerset.filter (fun s => s.card = k)

def leafCountSubgraph (G : SimpleGraph α) [DecidableRel G.Adj] (E_sub : Finset (Sym2 α)) : ℕ :=
  (Finset.univ.filter (fun v =>
    (Finset.univ.filter (fun u => Sym2.mk (v, u) ∈ E_sub)).card = 1
  )).card

def computableLs (G : SimpleGraph α) [DecidableRel G.Adj] (v0 : α) : ℕ :=
  let n_verts := Fintype.card α
  if n_verts ≤ 1 then 0 else
  let candidates := edgeSubsetsOfSize G (n_verts - 1)
  let connected_candidates := candidates.filter (fun s => isConnectedSubgraph G s v0)
  let leaf_counts := connected_candidates.image (fun s => leafCountSubgraph G s)
  (leaf_counts.max).getD 0

def toSubgraph' (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) : Subgraph G :=
  SimpleGraph.toSubgraph (SimpleGraph.fromEdgeSet (s : Set (Sym2 α))) (by
    intro u v h
    have h1 := h.1
    have h2 := h_sub h1
    rw [G.mem_edgeFinset] at h2
    exact h2)

-- ================================================================
-- Helper lemmas for Ls_eq_computable
-- ================================================================

omit [DecidableEq α]

private lemma toSubgraph_adj_iff' (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (w v : α) :
    (toSubgraph' G s h_sub).spanningCoe.Adj w v ↔ (Sym2.mk (w, v) ∈ s ∧ w ≠ v) := by
  unfold toSubgraph'
  simp only [Subgraph.spanningCoe_adj, toSubgraph_adj, fromEdgeSet_adj]
  exact Iff.rfl

private lemma toSubgraph_adj_of_mem_edge' (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset)
    (w v : α) (h_mem : Sym2.mk (w, v) ∈ s) :
    (toSubgraph' G s h_sub).spanningCoe.Adj w v := by
  rw [toSubgraph_adj_iff']
  refine ⟨h_mem, ?_⟩
  intro h_eq
  subst h_eq
  exact G.loopless w (G.mem_edgeFinset.mp (h_sub h_mem))

variable  [DecidableEq α]
private lemma mem_filter_of_adj' (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (w v : α)
    (hadj : (toSubgraph' G s h_sub).spanningCoe.Adj w v) :
    v ∈ Finset.univ.filter (fun u => Sym2.mk (w, u) ∈ s) := by
  rw [toSubgraph_adj_iff'] at hadj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hadj.1⟩

private lemma reachableStep_mono' (G : SimpleGraph α) [DecidableRel G.Adj]
    (E : Finset (Sym2 α)) : Monotone (reachableStep G E) := by
  intro A B h; unfold reachableStep
  exact Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

omit [Fintype α] [DecidableEq α] in
private lemma iterate_mono_finset (f : Finset α → Finset α)
    (hf : Monotone f) (n : ℕ) : Monotone (Nat.iterate f n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => intro a b h; simp only [Function.iterate_succ', Function.comp]; exact hf (ih h)

private lemma walk_endpoint_in_iterate (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset)
    (v0 v : α) (p : (toSubgraph' G s h_sub).spanningCoe.Walk v0 v) :
    v ∈ Nat.iterate (reachableStep G s) p.length {v0} := by
  induction p with
  | nil => exact Finset.mem_singleton.mpr rfl
  | @cons u w v hadj p ih =>
    rw [Walk.length_cons]
    have hw_step : w ∈ reachableStep G s {u} := by
      unfold reachableStep
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨u, Finset.mem_singleton.mpr rfl, mem_filter_of_adj' G s h_sub u w hadj⟩))
    have hw_iter1 : {w} ⊆ Nat.iterate (reachableStep G s) 1 {u} := by
      rw [Function.iterate_one]
      exact Finset.singleton_subset_iff.mpr hw_step
    have h_mono := iterate_mono_finset (reachableStep G s) (reachableStep_mono' G s) p.length hw_iter1
    rw [← Function.iterate_add_apply] at h_mono
    exact h_mono ih

private lemma mem_iterate_of_le' (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (v0 v : α) (k m : ℕ) (hkm : k ≤ m)
    (h : v ∈ Nat.iterate (reachableStep G s) k {v0}) :
    v ∈ Nat.iterate (reachableStep G s) m {v0} := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hkm
  induction d with
  | zero => exact h
  | succ d ih_d =>
    rw [Nat.add_succ]
    exact (iterate_mono_finset (reachableStep G s) (reachableStep_mono' G s) (k + d)
      (by unfold reachableStep; exact Finset.subset_union_left)) (ih_d (Nat.le_add_right k d))

lemma iterate_reachableStep_subset_reachable (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (k : ℕ) (a : Finset α) (v : α)
    (h : v ∈ (Nat.iterate (reachableStep G s) k) a) :
    ∃ u ∈ a, (toSubgraph' G s h_sub).spanningCoe.Reachable u v := by
  induction k generalizing a v with
  | zero => exact ⟨v, h, Reachable.rfl⟩
  | succ k ih =>
    set b := Nat.iterate (reachableStep G s) k a
    rw [Function.iterate_succ_apply' (reachableStep G s) k a] at h
    rcases Finset.mem_union.mp
      (by unfold reachableStep at h; exact h : v ∈ b ∪ _) with h1 | h2
    · exact ih _ _ h1
    · obtain ⟨w, hw1, hw2⟩ := Finset.mem_biUnion.mp h2
      obtain ⟨u, hu, huw⟩ := ih _ w hw1
      exact ⟨u, hu, Reachable.trans huw ⟨Walk.cons (toSubgraph_adj_of_mem_edge' G s h_sub w v
        (Finset.mem_filter.mp hw2).2) Walk.nil⟩⟩

lemma mem_iterate_reachableStep_iff_reachable (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (v0 v : α) :
    v ∈ (Nat.iterate (reachableStep G s) (Fintype.card α)) {v0} ↔
      (toSubgraph' G s h_sub).spanningCoe.Reachable v0 v := by
  constructor
  · intro h; obtain ⟨u, hu, huv⟩ := iterate_reachableStep_subset_reachable G s h_sub _ _ _ h
    rwa [Finset.mem_singleton.mp hu] at huv
  · intro ⟨p⟩; exact mem_iterate_of_le' G s v0 v p.toPath.val.length (Fintype.card α)
      (Nat.le_of_lt (Walk.IsPath.length_lt p.toPath.prop))
      (walk_endpoint_in_iterate G s h_sub v0 v p.toPath.val)

-- ================================================================
-- Connected subgraph ↔
-- ================================================================

private lemma isConnectedSubgraph_iff (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (v0 : α) :
    isConnectedSubgraph G s v0 = true ↔
    (toSubgraph' G s h_sub).spanningCoe.Connected := by
  unfold isConnectedSubgraph
  simp only [decide_eq_true_eq]
  constructor
  · intro h_card
    have h_all : Nat.iterate (reachableStep G s) (Fintype.card α) {v0} = Finset.univ :=
      Finset.eq_univ_of_card _ h_card
    have h_ne : Nonempty α := ⟨v0⟩
    exact Connected.mk (fun u v => by
      have hu : u ∈ Nat.iterate (reachableStep G s) (Fintype.card α) {v0} :=
        h_all ▸ Finset.mem_univ u
      have hv : v ∈ Nat.iterate (reachableStep G s) (Fintype.card α) {v0} :=
        h_all ▸ Finset.mem_univ v
      have hu' : (toSubgraph' G s h_sub).spanningCoe.Reachable v0 u := by
        rwa [mem_iterate_reachableStep_iff_reachable G s h_sub v0 u] at hu
      have hv' : (toSubgraph' G s h_sub).spanningCoe.Reachable v0 v := by
        rwa [mem_iterate_reachableStep_iff_reachable G s h_sub v0 v] at hv
      exact hu'.symm.trans hv')
  · intro hconn
    have : Nat.iterate (reachableStep G s) (Fintype.card α) {v0} = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun v => (mem_iterate_reachableStep_iff_reachable
        G s h_sub v0 v).mpr (hconn.preconnected v0 v))
    rw [this, Finset.card_univ]

-- ================================================================
-- Edge set correspondence
-- ================================================================
omit [DecidableEq α] in
private lemma toSubgraph'_edgeFinset_eq (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) :
    (toSubgraph' G s h_sub).spanningCoe.edgeFinset = s := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [mem_edgeFinset, mem_edgeSet]
    rw [toSubgraph_adj_iff']
    constructor
    · exact fun ⟨h1, _⟩ => h1
    · intro h1
      exact ⟨h1, fun heq => by subst heq; exact G.loopless a (G.mem_edgeFinset.mp (h_sub h1))⟩

-- ================================================================
-- Leaf count correspondence
-- ================================================================

private lemma toSubgraph'_degree_eq (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) (v : α) :
    (toSubgraph' G s h_sub).degree v =
    (Finset.univ.filter (fun u => Sym2.mk (v, u) ∈ s)).card := by
  unfold Subgraph.degree
  have h_eq : Set.toFinset ((toSubgraph' G s h_sub).neighborSet v) = Finset.univ.filter (fun u => Sym2.mk (v, u) ∈ s) := by
    ext w
    simp only [Set.mem_toFinset, Subgraph.mem_neighborSet]
    unfold toSubgraph'
    simp only [toSubgraph_adj, fromEdgeSet_adj]
    constructor
    · exact fun ⟨h1, _⟩ => Finset.mem_filter.mpr ⟨Finset.mem_univ w, h1⟩
    · intro h; rw [Finset.mem_filter] at h
      exact ⟨h.2, fun heq => by subst heq; exact G.loopless v (G.mem_edgeFinset.mp (h_sub h.2))⟩
  rw [← Set.toFinset_card]
  exact congr_arg Finset.card h_eq

private lemma leaf_count_eq_leaves (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) :
    leafCountSubgraph G s =
    (Finset.univ.filter (fun v => (toSubgraph' G s h_sub).degree v = 1)).card := by
  unfold leafCountSubgraph; congr 1; ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [toSubgraph'_degree_eq]

-- ================================================================
-- toSubgraph'.IsSpanning
-- ================================================================

omit [DecidableEq α]

private lemma toSubgraph'_isSpanning (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset (Sym2 α)) (h_sub : s ⊆ G.edgeFinset) :
    (toSubgraph' G s h_sub).IsSpanning :=
  SimpleGraph.toSubgraph.isSpanning _ _

-- ================================================================
-- Helper lemmas for main inequalities
-- ================================================================

private lemma Ls_bddAbove (G : SimpleGraph α) [DecidableRel G.Adj] :
    BddAbove (Set.image (fun T =>
        ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ))
        { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }) := by
  use (Fintype.card α : ℝ)
  rintro x ⟨T, ⟨hspan, _⟩, rfl⟩
  push_cast
  have h_verts : T.verts.toFinset = Finset.univ := by
    ext v; simp [hspan v]
  rw [h_verts]
  exact_mod_cast Finset.card_filter_le _ _

private lemma Ls_nonneg (G : SimpleGraph α) [DecidableRel G.Adj] : 0 ≤ Ls G := by
  unfold Ls
  by_cases h : ∃ T : Subgraph G, T.IsSpanning ∧ IsTree T.coe
  · rcases h with ⟨T, hspan, htree⟩
    apply le_csSup_of_le (Ls_bddAbove G)
      (b := ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ))
    · exact ⟨T, ⟨hspan, htree⟩, rfl⟩
    · positivity
  · push_neg at h
    have h_empty : { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe } = ∅ := by
      ext T; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ⟨a, b⟩ => h T a b
    rw [h_empty, Set.image_empty]
    exact le_of_eq Real.sSup_empty.symm

private lemma spanning_tree_edge_card (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : Subgraph G) (h_span : T.IsSpanning) (h_tree : IsTree T.coe) :
    T.edgeSet.toFinset.card + 1 = Fintype.card α := by
  have h_iso := T.spanningCoeEquivCoeOfSpanning h_span
  have h_tree_span : IsTree T.spanningCoe := h_iso.symm.isTree_iff.mp h_tree
  have h_card := h_tree_span.card_edgeFinset
  have h_edge_eq : T.spanningCoe.edgeFinset = T.edgeSet.toFinset := by
    ext e
    simp only [mem_edgeFinset]
    induction e using Sym2.ind with
    | h a b => simp [Subgraph.spanningCoe_adj, Subgraph.mem_edgeSet, Set.mem_toFinset]
  rw [h_edge_eq] at h_card
  exact h_card

private lemma spanning_tree_size_mem (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : Subgraph G) (h_span : T.IsSpanning) (h_tree : IsTree T.coe) :
    T.edgeSet.toFinset ∈ G.edgeSubsetsOfSize (Fintype.card α - 1) := by
  unfold edgeSubsetsOfSize
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro e he
    rw [Set.mem_toFinset] at he
    exact Set.mem_toFinset.mpr (T.edgeSet_subset he)
  · have := spanning_tree_edge_card G T h_span h_tree
    omega

-- ================================================================
-- Main inequalities
-- ================================================================
variable [DecidableEq α]

theorem Ls_le_computableLs (G : SimpleGraph α) [DecidableRel G.Adj] (v0 : α) :
    Ls G ≤ (computableLs G v0 : ℝ) := by
  by_cases h_card : Fintype.card α ≤ 1
  · -- card ≤ 1: computableLs is 0, Ls is nonneg but also ≤ 0
    -- In fact any spanning tree has no leaves when |V| ≤ 1
    unfold Ls computableLs
    simp only [if_pos h_card, Nat.cast_zero]
    by_cases h_span : ∃ T : Subgraph G, T.IsSpanning ∧ IsTree T.coe
    · apply csSup_le
      · rcases h_span with ⟨T, hsp, htr⟩
        exact ⟨_, ⟨T, ⟨hsp, htr⟩, rfl⟩⟩
      · rintro x ⟨T, ⟨hspan, htree⟩, rfl⟩
        show ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ) ≤ 0
        have h1 : Fintype.card α ≤ 1 := h_card
        have h_edge := spanning_tree_edge_card G T hspan htree
        have h_no_edges : T.edgeSet.toFinset.card = 0 := by omega
        have h_deg_zero : ∀ v, T.degree v = 0 := by
          intro v
          unfold Subgraph.degree
          rw [Fintype.card_eq_zero_iff, isEmpty_subtype]
          intro w
          by_contra hw
          have : Sym2.mk (v, w) ∈ T.edgeSet.toFinset := by
            rw [Set.mem_toFinset, Subgraph.mem_edgeSet]
            exact hw
          rw [Finset.card_eq_zero] at h_no_edges
          simp [h_no_edges] at this
        simp [h_deg_zero]
    · push_neg at h_span
      have h_empty : { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe } = ∅ := by
        ext T; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨a, b⟩ => h_span T a b
      rw [h_empty, Set.image_empty]
      exact le_of_eq Real.sSup_empty
  · unfold Ls
    by_cases h_span : ∃ T : Subgraph G, T.IsSpanning ∧ IsTree T.coe
    · rcases h_span with ⟨T, h_span_T, h_tree_T⟩
      apply csSup_le
      · -- show nonempty set
        have h_verts : T.verts.toFinset = Finset.univ := by
          ext v; simp [h_span_T v]
        exact ⟨_, ⟨T, ⟨h_span_T, h_tree_T⟩, rfl⟩⟩
      · rintro x ⟨T', ⟨h_span_T', h_tree_T'⟩, h_leaf⟩
        show x ≤ (computableLs G v0 : ℝ)
        rw [← h_leaf]
        show ((T'.verts.toFinset.filter (fun v => T'.degree v = 1)).card : ℝ) ≤ _
        set s := T'.edgeSet.toFinset
        have h_size := spanning_tree_size_mem G T' h_span_T' h_tree_T'
        have h_sub : s ⊆ G.edgeFinset := by
          unfold edgeSubsetsOfSize at h_size
          have h_mem_powerset := (Finset.mem_filter.mp h_size).1
          rw [Finset.mem_powerset] at h_mem_powerset
          exact h_mem_powerset
        have : Nonempty α := ⟨v0⟩
        -- T' is connected (from IsTree), and T' = toSubgraph' s, so
        -- the spanning coe is connected
        have h_subgraph_eq : T' = G.toSubgraph' s h_sub := by
          ext v
          · exact ⟨fun _ => Set.mem_univ v, fun _ => h_span_T' v⟩
          · next u v =>
            constructor
            · intro hadj
              unfold toSubgraph'
              simp only [toSubgraph_adj, fromEdgeSet_adj]
              exact ⟨Set.mem_toFinset.mpr (Subgraph.mem_edgeSet.mpr hadj),
                     (T'.adj_sub hadj).ne⟩
            · intro hadj
              unfold toSubgraph' at hadj
              simp only [toSubgraph_adj, fromEdgeSet_adj] at hadj
              exact Subgraph.mem_edgeSet.mp (Set.mem_toFinset.mp hadj.1)
        have h_conn : G.isConnectedSubgraph s v0 = true := by
          rw [isConnectedSubgraph_iff G s h_sub]
          have : (G.toSubgraph' s h_sub).spanningCoe = T'.spanningCoe := by
            rw [h_subgraph_eq]
          rw [this]
          have h_iso := T'.spanningCoeEquivCoeOfSpanning h_span_T'
          exact h_iso.connected_iff.mpr h_tree_T'.isConnected
        -- The leaf count of T' equals leafCountSubgraph s
        have h_leaf_eq : (T'.verts.toFinset.filter (fun v => T'.degree v = 1)).card =
            G.leafCountSubgraph s := by
          rw [h_subgraph_eq, leaf_count_eq_leaves]
          have h_verts_eq : (toSubgraph' G s h_sub).verts.toFinset = Finset.univ := by
            ext v; simp [toSubgraph'_isSpanning G s h_sub v]
          rw [h_verts_eq]
        rw [h_leaf_eq]
        -- leafCountSubgraph s ≤ computableLs G v0
        unfold computableLs
        rw [if_neg h_card]
        -- Goal: ↑(leafCountSubgraph G s) ≤ ↑(Option.getD counts.max 0)
        have h_mem_counts : G.leafCountSubgraph s ∈
            (image (fun s => G.leafCountSubgraph s)
              (filter (fun s => G.isConnectedSubgraph s v0 = true)
                (G.edgeSubsetsOfSize (Fintype.card α - 1)))) := by
          rw [mem_image]
          exact ⟨s, mem_filter.mpr ⟨h_size, h_conn⟩, rfl⟩
        have h_le := Finset.le_max h_mem_counts
        push_cast
        generalize h_max : (image (fun s => G.leafCountSubgraph s)
              (filter (fun s => G.isConnectedSubgraph s v0 = true)
                (G.edgeSubsetsOfSize (Fintype.card α - 1)))).max = o_max at h_le
        rcases o_max with _ | v
        · exact absurd h_le (not_le.mpr (WithBot.bot_lt_coe _))
        · simp only [Option.getD_some]
          exact_mod_cast WithBot.coe_le_coe.mp h_le
    · -- no spanning trees: sSup of empty set
      push_neg at h_span
      have h_empty : { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe } = ∅ := by
        ext T; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨a, b⟩ => h_span T a b
      rw [h_empty, Set.image_empty]
      rw [Real.sSup_empty]
      exact_mod_cast Nat.zero_le _

theorem computableLs_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj] (v0 : α) :
    (computableLs G v0 : ℝ) ≤ Ls G := by
  by_cases h : Fintype.card α ≤ 1
  · -- computableLs is 0 when card ≤ 1
    have h_eq : computableLs G v0 = 0 := by
      unfold computableLs; simp [if_pos h]
    rw [h_eq]; push_cast; exact Ls_nonneg G
  · -- Suffices to show: for any s in the candidates, leafCountSubgraph s ≤ Ls
    -- and then max of those ≤ Ls
    -- Strategy: show computableLs ≤ max leaf count ≤ Ls
    suffices h_suff : ∀ s ∈ filter (fun s => G.isConnectedSubgraph s v0 = true)
        (G.edgeSubsetsOfSize (Fintype.card α - 1)),
        (G.leafCountSubgraph s : ℝ) ≤ Ls G by
      unfold computableLs
      rw [if_neg h]
      push_cast
      -- Need: Option.getD (...).max 0 ≤ Ls G
      -- Case analysis on whether there are any candidates
      generalize h_max_eq : (image (fun s => G.leafCountSubgraph s)
          (filter (fun s => G.isConnectedSubgraph s v0 = true)
            (G.edgeSubsetsOfSize (Fintype.card α - 1)))).max = o_max
      rcases o_max with _ | M
      · -- Empty: getD gives 0, and 0 ≤ Ls G
        simp only [Option.getD_none]
        push_cast
        exact Ls_nonneg G
      · simp only [Option.getD_some]
        have h_M_mem := Finset.mem_of_max h_max_eq
        rcases Finset.mem_image.mp h_M_mem with ⟨s, hs, rfl⟩
        exact h_suff s hs
    -- Now prove the main claim: for each candidate s, leaf_count ≤ Ls
    intro s hs
    rw [Finset.mem_filter] at hs
    have h_size := hs.1
    have h_conn := hs.2
    unfold edgeSubsetsOfSize at h_size
    rw [Finset.mem_filter] at h_size
    have h_sub : s ⊆ G.edgeFinset := by
      rw [Finset.mem_powerset] at h_size; exact h_size.1
    have h_card_s : s.card = Fintype.card α - 1 := h_size.2
    -- Build the spanning tree from s
    have h_spanning := toSubgraph'_isSpanning G s h_sub
    have h_iso := (toSubgraph' G s h_sub).spanningCoeEquivCoeOfSpanning h_spanning
    have h_conn_spanningCoe : (toSubgraph' G s h_sub).spanningCoe.Connected := by
      rwa [isConnectedSubgraph_iff G s h_sub] at h_conn
    have h_tree : IsTree (toSubgraph' G s h_sub).coe := by
      rw [h_iso.symm.isTree_iff, isTree_iff_connected_and_card]
      refine ⟨h_conn_spanningCoe, ?_⟩
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      have h_edge_card : Fintype.card (toSubgraph' G s h_sub).spanningCoe.edgeSet = s.card := by
        rw [← edgeFinset_card]
        congr 1
        exact toSubgraph'_edgeFinset_eq G s h_sub
      rw [h_edge_card, h_card_s]
      omega
    -- leafCountSubgraph s ≤ Ls G since toSubgraph' is a spanning tree
    unfold Ls
    apply le_csSup (Ls_bddAbove G)
    refine ⟨toSubgraph' G s h_sub, ⟨h_spanning, h_tree⟩, ?_⟩
    simp only
    rw [leaf_count_eq_leaves G s h_sub]
    have h_verts_eq : (toSubgraph' G s h_sub).verts.toFinset = Finset.univ := by
      ext v; simp [h_spanning v]
    rw [h_verts_eq]

theorem Ls_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] (v0 : α) :
    Ls G = (computableLs G v0 : ℝ) := by
  exact le_antisymm (Ls_le_computableLs G v0) (computableLs_le_Ls G v0)

/-- A unit distance graph in ℝ²:
A graph where the vertices V are a collection of points in ℝ² and there is
an edge between two points if and only if the distance between them is 1. -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := Dist.dist x y = 1
  symm x y := by simp [PseudoMetricSpace.dist_comm]

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths. Note that graphs with at most one vertex are not classed as
infinitely connected.
-/
def InfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop := Nontrivial V ∧
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/-- Infinite graphs: definitions for max degree and clique number so that the maximum
degree (resp. clique number) of a graph with unbounded degree (resp. clique size) is
`∞` rather than 0.
-/
noncomputable
def edegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ∞ := (G.neighborSet v).encard

noncomputable
def emaxDegree {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ v, G.edegree v

noncomputable
def ecliqueNum {V : Type} (G : SimpleGraph V) : ℕ∞ := ⨆ (s : Finset V) (_ : G.IsClique s), #s

-- ================================================================
-- Computable graph invariants for testing
-- ================================================================

/-- BFS expansion: add all neighbors of S to S. -/
def bfs_expand (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Finset α :=
  S ∪ S.biUnion (fun v => Finset.univ.filter (G.Adj v))

def bfs_dist_aux [DecidableEq α] [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (target : α) :
    ℕ → ℕ → Finset α → ℕ
  | 0, _, _ => 0
  | fuel + 1, depth, reached =>
    if target ∈ reached then depth
    else bfs_dist_aux G target fuel (depth + 1) (bfs_expand G reached)

/-- Computable graph distance via BFS.
Returns 0 if u = v or if v is unreachable from u. -/
def computable_dist (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℕ :=
  if u = v then 0
  else bfs_dist_aux G v (Fintype.card α) 1 (bfs_expand G {u})

/-- Computable independence number via powerset enumeration. -/
def computable_indep_num (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter (fun s : Finset α =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v)).sup Finset.card

/-- Computable domination number via powerset enumeration. -/
def computable_dom_num (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.powerset.filter (fun D : Finset α =>
    ∀ v : α, v ∈ D ∨ ∃ w ∈ D, G.Adj v w)).inf'
    ⟨Finset.univ, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
       fun v => Or.inl (Finset.mem_univ v)⟩⟩
    Finset.card

/-- Computable Wiener index: half the sum of all ordered pairwise distances. -/
def computable_wiener (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, computable_dist G u v) / 2

/-- Computable average distance as a rational. -/
def computable_avg_dist (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  if Fintype.card α > 1 then
    (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (computable_dist G u v : ℚ)) /
      ((Fintype.card α : ℚ) * ((Fintype.card α : ℚ) - 1))
  else 0

/-- Computable Szeged auxiliary: count vertices closer to u than v. -/
def computable_szeged_aux (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℕ :=
  (Finset.univ.filter (fun w => computable_dist G w u < computable_dist G w v)).card

/-- Computable Szeged index. -/
def computable_szeged_index (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => computable_szeged_aux G u v * computable_szeged_aux G v u,
      fun a b => by ring⟩ e

end SimpleGraph
