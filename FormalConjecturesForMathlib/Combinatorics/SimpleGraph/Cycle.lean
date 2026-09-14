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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A cycle of `G`, carrying its basepoint. Bundling the basepoint makes the cycles of `G` into a
type, so they can be collected into a `Finset` or a `Multiset`. -/
structure Cycle (G : SimpleGraph V) where
  /-- The vertex the cycle starts and ends at. -/
  base : V
  /-- The closed walk tracing the cycle. -/
  walk : G.Walk base base
  /-- That walk is a cycle. -/
  isCycle : walk.IsCycle

/-- The edges a cycle traverses. -/
def Cycle.edges {G : SimpleGraph V} (c : Cycle G) : List (Sym2 V) := c.walk.edges

/-- The length of a cycle, its number of edges. -/
def Cycle.length {G : SimpleGraph V} (c : Cycle G) : ℕ := c.walk.length

/-- The chords (also called diagonals) of a cycle: edges of `G` that join two vertices of
the cycle and are not themselves edges of the cycle. -/
def Cycle.chords {G : SimpleGraph V} (c : Cycle G) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ c.walk.support) ∧ e ∉ c.edges}

lemma Cycle.chords_subset_edgeSet {G : SimpleGraph V} (c : Cycle G) :
    c.chords ⊆ G.edgeSet := fun _ he ↦ he.1

@[simp]
lemma Cycle.mem_chords {G : SimpleGraph V} {c : Cycle G} {e : Sym2 V} :
    e ∈ c.chords ↔ e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ c.walk.support) ∧ e ∉ c.edges :=
  Iff.rfl

/-- `G` contains an odd cycle with at least `k` chords (also called diagonals). -/
def HasOddCycleWithChords (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Cycle G, Odd c.length ∧ k ≤ c.chords.encard

lemma HasOddCycleWithChords.mono {G : SimpleGraph V} {k k' : ℕ}
    (h : HasOddCycleWithChords G k) (hle : k' ≤ k) : HasOddCycleWithChords G k' := by
  obtain ⟨c, hodd, hk⟩ := h
  exact ⟨c, hodd, (Nat.cast_le.mpr hle).trans hk⟩

/-- For `k = 0`, having an odd cycle with at least `k` chords is exactly having an odd cycle. -/
lemma HasOddCycleWithChords.zero_iff {G : SimpleGraph V} :
    HasOddCycleWithChords G 0 ↔ ∃ c : Cycle G, Odd c.length :=
  ⟨fun ⟨c, hodd, _⟩ ↦ ⟨c, hodd⟩, fun ⟨c, hodd⟩ ↦ ⟨c, hodd, bot_le⟩⟩

/-- Chords are never edges of the underlying cycle walk. -/
lemma Cycle.not_mem_edges_of_mem_chords {G : SimpleGraph V} {c : Cycle G} {e : Sym2 V}
    (he : e ∈ c.chords) : e ∉ c.edges :=
  (mem_chords.mp he).2.2

/-- The set of chords is disjoint from the set of cycle edges. -/
lemma Cycle.chords_disjoint_edges {G : SimpleGraph V} (c : Cycle G) :
    Disjoint c.chords {e | e ∈ c.edges} := by
  refine Set.disjoint_left.2 fun e he ↦ ?_
  simp [not_mem_edges_of_mem_chords he]

/-- Endpoints of a chord lie on the cycle. -/
lemma Cycle.mem_support_of_mem_chords {G : SimpleGraph V} {c : Cycle G} {e : Sym2 V}
    (he : e ∈ c.chords) : ∀ v ∈ e, v ∈ c.walk.support :=
  (mem_chords.mp he).2.1

/-- Having an odd cycle with enough chords implies having some odd cycle. -/
lemma HasOddCycleWithChords.exists_odd_cycle {G : SimpleGraph V} {k : ℕ}
    (h : HasOddCycleWithChords G k) : ∃ c : Cycle G, Odd c.length := by
  obtain ⟨c, hodd, _⟩ := h
  exact ⟨c, hodd⟩

/-- Every bundled cycle has length at least `3`. -/
lemma Cycle.three_le_length {G : SimpleGraph V} (c : Cycle G) : 3 ≤ c.length :=
  c.isCycle.three_le_length

/-- The length of a bundled cycle lies in `G.cycleLengths`. -/
lemma Cycle.length_mem_cycleLengths {G : SimpleGraph V} (c : Cycle G) :
    c.length ∈ G.cycleLengths :=
  ⟨c.base, c.walk, c.isCycle, rfl⟩

/-- An odd bundled cycle contributes an odd length to `oddCycleLengths`. -/
lemma Cycle.mem_oddCycleLengths_of_odd {G : SimpleGraph V} (c : Cycle G) (h : Odd c.length) :
    c.length ∈ G.oddCycleLengths :=
  ⟨c.length_mem_cycleLengths, h⟩

/-- Having an odd cycle with chords yields a nonempty `oddCycleLengths` set. -/
lemma HasOddCycleWithChords.oddCycleLengths_nonempty {G : SimpleGraph V} {k : ℕ}
    (h : HasOddCycleWithChords G k) : G.oddCycleLengths.Nonempty := by
  obtain ⟨c, hodd, _⟩ := h
  exact ⟨c.length, c.mem_oddCycleLengths_of_odd hodd⟩

/-- Chords form a subset of the edge set, so their `encard` is bounded by that of `edgeSet`. -/
lemma Cycle.encard_chords_le_encard_edgeSet {G : SimpleGraph V} (c : Cycle G) :
    c.chords.encard ≤ G.edgeSet.encard :=
  Set.encard_le_encard c.chords_subset_edgeSet

/-- Bundled cycles have positive length. -/
lemma Cycle.length_pos {G : SimpleGraph V} (c : Cycle G) : 0 < c.length :=
  lt_of_lt_of_le (by decide : (0 : ℕ) < 3) c.three_le_length

/-- Reverse a bundled cycle (same length). -/
def Cycle.reverse {G : SimpleGraph V} (c : Cycle G) : Cycle G where
  base := c.base
  walk := c.walk.reverse
  isCycle := c.isCycle.reverse

@[simp]
lemma Cycle.length_reverse {G : SimpleGraph V} (c : Cycle G) : c.reverse.length = c.length := by
  simp [reverse, length]

@[simp]
lemma Cycle.reverse_reverse {G : SimpleGraph V} (c : Cycle G) : c.reverse.reverse = c := by
  cases c
  simp [reverse]

/-- Reversing a cycle does not change its chord set. -/
@[simp]
lemma Cycle.chords_reverse {G : SimpleGraph V} (c : Cycle G) : c.reverse.chords = c.chords := by
  ext e
  simp [chords, reverse, edges, Walk.edges_reverse, List.mem_reverse, Walk.support_reverse,
    List.mem_reverse]

/-- A bundled cycle's length is odd iff it lies in `oddCycleLengths`. -/
lemma Cycle.mem_oddCycleLengths_iff_odd {G : SimpleGraph V} (c : Cycle G) :
    c.length ∈ G.oddCycleLengths ↔ Odd c.length :=
  ⟨And.right, fun h ↦ c.mem_oddCycleLengths_of_odd h⟩

/-- Every member of `cycleLengths` is the length of some bundled `Cycle`. -/
lemma exists_cycle_of_mem_cycleLengths {G : SimpleGraph V} {m : ℕ}
    (hm : m ∈ G.cycleLengths) : ∃ c : Cycle G, c.length = m := by
  obtain ⟨a, w, hc, rfl⟩ := hm
  exact ⟨⟨a, w, hc⟩, rfl⟩

lemma mem_cycleLengths_iff_exists_cycle {G : SimpleGraph V} {m : ℕ} :
    m ∈ G.cycleLengths ↔ ∃ c : Cycle G, c.length = m :=
  ⟨exists_cycle_of_mem_cycleLengths, fun ⟨c, hc⟩ ↦ hc ▸ c.length_mem_cycleLengths⟩

/-- Odd members of `oddCycleLengths` are witnessed by odd bundled cycles. -/
lemma exists_cycle_of_mem_oddCycleLengths {G : SimpleGraph V} {m : ℕ}
    (hm : m ∈ G.oddCycleLengths) : ∃ c : Cycle G, c.length = m ∧ Odd c.length := by
  obtain ⟨hm', hodd⟩ := mem_oddCycleLengths_iff.mp hm
  obtain ⟨c, rfl⟩ := exists_cycle_of_mem_cycleLengths hm'
  exact ⟨c, rfl, hodd⟩

/-- `HasOddCycleWithChords G 0` iff `oddCycleLengths` is nonempty. -/
lemma HasOddCycleWithChords.zero_iff_oddCycleLengths_nonempty {G : SimpleGraph V} :
    HasOddCycleWithChords G 0 ↔ G.oddCycleLengths.Nonempty := by
  constructor
  · exact oddCycleLengths_nonempty
  · intro ⟨m, hm⟩
    obtain ⟨c, rfl, hodd⟩ := exists_cycle_of_mem_oddCycleLengths hm
    exact ⟨c, hodd, bot_le⟩

/-- `G` is bridgeless if none of its edges is a bridge. -/
def IsBridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

/-- The empty graph is bridgeless. -/
@[simp]
lemma isBridgeless_bot : IsBridgeless (⊥ : SimpleGraph V) := by
  intro e he
  exact (SimpleGraph.edgeSet_bot ▸ he).elim

/-- Graphs with no edges are bridgeless. -/
lemma isBridgeless_of_edgeSet_eq_empty {G : SimpleGraph V} (h : G.edgeSet = ∅) :
    IsBridgeless G := by
  intro e he
  exact (h ▸ he).elim

/-- An edge of a cycle is never a bridge. -/
lemma Cycle.not_isBridge_of_mem_edges {G : SimpleGraph V} (c : Cycle G) {e : Sym2 V}
    (he : e ∈ c.edges) : ¬ G.IsBridge e :=
  fun hbr ↦ hbr.notMem_edges_of_isCycle c.isCycle he

/-- If every edge lies on some cycle, then `G` is bridgeless. -/
lemma IsBridgeless.of_forall_exists_cycle_mem_edges {G : SimpleGraph V}
    (h : ∀ e ∈ G.edgeSet, ∃ c : Cycle G, e ∈ c.edges) : IsBridgeless G := by
  intro e he hbr
  obtain ⟨c, hc⟩ := h e he
  exact c.not_isBridge_of_mem_edges hc hbr

/-- An odd cycle (even without chords) witnesses that `G` is not acyclic. -/
lemma not_isAcyclic_of_hasOddCycleWithChords {G : SimpleGraph V} {k : ℕ}
    (h : HasOddCycleWithChords G k) : ¬ G.IsAcyclic := by
  obtain ⟨c, _, _⟩ := h
  exact fun hacyc ↦ hacyc c.walk c.isCycle

/-- In a forest every edge is a bridge, so an acyclic bridgeless graph has no edges at all. -/
theorem edgeFinset_eq_empty_of_isBridgeless_of_isAcyclic [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hbr : G.IsBridgeless) : G.edgeFinset = ∅ := by
  rw [SimpleGraph.edgeFinset_eq_empty]
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hadj
  exact hbr s(u, v) hadj (G.isAcyclic_iff_forall_isBridge.mp hacyc hadj)


/-- A bridgeless graph with at least one edge is not a forest. -/
lemma IsBridgeless.not_isAcyclic_of_mem_edgeSet {G : SimpleGraph V}
    (h : IsBridgeless G) {e : Sym2 V} (he : e ∈ G.edgeSet) : ¬ G.IsAcyclic := by
  intro hacyc
  exact h e he (isAcyclic_iff_forall_isBridge.mp hacyc he)

/-- The edges of the Eulerian cycle of `cycleGraph (n + 3)` are exactly all of its edges. -/
lemma cycleGraph_edgeFinset_eq_cycle_edges (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset = (cycleGraph.cycle n).edges.toFinset := by
  classical
  let G := cycleGraph (n + 3)
  let c := cycleGraph.cycle n
  have hnodup : c.edges.Nodup := cycleGraph.isCycle_cycle.isTrail.edges_nodup
  have hsub : c.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    simpa [mem_edgeFinset] using Walk.edges_subset_edgeSet c (List.mem_toFinset.mp he)
  have hclen : c.edges.toFinset.card = n + 3 := by
    rw [List.toFinset_card_of_nodup hnodup, Walk.length_edges, cycleGraph.length_cycle]
  have hdeg : ∀ v : Fin (n + 3), G.degree v = 2 := fun _ => cycleGraph_degree_three_le
  have hGcard : G.edgeFinset.card = n + 3 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    -- `(n + 3) * 2 = 2 * #edges`
    have : (n + 3) * 2 = 2 * G.edgeFinset.card := by simpa using hsum
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hGcard, hclen])).symm

/-- Every edge of `cycleGraph (n + 3)` lies on its Eulerian cycle. -/
lemma mem_cycleGraph_cycle_edges_of_mem_edgeSet {n : ℕ} {e : Sym2 (Fin (n + 3))}
    (he : e ∈ (cycleGraph (n + 3)).edgeSet) :
    e ∈ (cycleGraph.cycle n).edges := by
  classical
  have h := cycleGraph_edgeFinset_eq_cycle_edges n
  have : e ∈ (cycleGraph (n + 3)).edgeFinset := by
    simpa [SimpleGraph.mem_edgeFinset] using he
  rw [h] at this
  exact List.mem_toFinset.mp this

/-- Hence `cycleGraph (n + 3)` is bridgeless. -/
theorem cycleGraph_isBridgeless (n : ℕ) : IsBridgeless (cycleGraph (n + 3)) :=
  IsBridgeless.of_forall_exists_cycle_mem_edges fun _e he =>
    ⟨⟨0, cycleGraph.cycle n, cycleGraph.isCycle_cycle⟩, mem_cycleGraph_cycle_edges_of_mem_edgeSet he⟩

/-- Bundled form of the Eulerian cycle of `cycleGraph (n + 3)`. -/
def Cycle.cycleGraph (n : ℕ) : Cycle (cycleGraph (n + 3)) :=
  ⟨0, cycleGraph.cycle n, cycleGraph.isCycle_cycle⟩

@[simp]
lemma Cycle.length_cycleGraph (n : ℕ) : (Cycle.cycleGraph n).length = n + 3 :=
  cycleGraph.length_cycle



/-- The Eulerian cycle of `cycleGraph` has no chords: every edge of the graph is a cycle edge. -/
theorem Cycle.cycleGraph_chords_eq_empty (n : ℕ) :
    (Cycle.cycleGraph n).chords = ∅ := by
  ext e
  simp only [mem_chords, Set.mem_empty_iff_false, iff_false]
  rintro ⟨he, _hsup, hnotin⟩
  exact hnotin (mem_cycleGraph_cycle_edges_of_mem_edgeSet he)

@[simp]
lemma Cycle.cycleGraph_chords_encard (n : ℕ) :
    (Cycle.cycleGraph n).chords.encard = 0 := by
  simp [cycleGraph_chords_eq_empty]

/-- Odd cycle graphs have an odd cycle with (at least) `0` chords. -/
lemma hasOddCycleWithChords_cycleGraph_zero {n : ℕ} (h : Odd (n + 3)) :
    HasOddCycleWithChords (cycleGraph (n + 3)) 0 :=
  ⟨Cycle.cycleGraph n, by simpa [Cycle.length_cycleGraph] using h, bot_le⟩

/-- Every `cycleGraph (n + 3)` contains a cycle, so it is never a forest. -/
theorem cycleGraph_not_isAcyclic (n : ℕ) : ¬ (cycleGraph (n + 3)).IsAcyclic :=
  fun hacyc ↦ hacyc (cycleGraph.cycle n) cycleGraph.isCycle_cycle

/-- The odd-length case is the unconditional statement. -/
lemma cycleGraph_not_isAcyclic_of_odd {n : ℕ} (_h : Odd (n + 3)) :
    ¬ (cycleGraph (n + 3)).IsAcyclic :=
  cycleGraph_not_isAcyclic n

/-- The cycle graph on `n + 3` vertices has exactly `n + 3` edges. -/
lemma cycleGraph_card_edgeFinset (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  classical
  have hdeg : ∀ v : Fin (n + 3), (cycleGraph (n + 3)).degree v = 2 :=
    fun _ => cycleGraph_degree_three_le
  have hsum := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have : (n + 3) * 2 = 2 * (cycleGraph (n + 3)).edgeFinset.card := by simpa using hsum
  omega

/-- Nonempty edge set of `cycleGraph`, via the card formula. -/
lemma cycleGraph_edgeFinset_nonempty (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.Nonempty := by
  rw [Finset.card_pos.symm, cycleGraph_card_edgeFinset]
  omega

/-- A bundled cycle's edge list has the same length as the cycle. -/
@[simp]
lemma Cycle.edges_length {G : SimpleGraph V} (c : Cycle G) : c.edges.length = c.length :=
  Walk.length_edges _

/-- Cycle edges are nodup (cycles are trails). -/
lemma Cycle.edges_nodup {G : SimpleGraph V} (c : Cycle G) : c.edges.Nodup :=
  c.isCycle.isTrail.edges_nodup

/-- Eulerian cycle of `C_{n+3}` traverses exactly `n+3` edges. -/
@[simp]
lemma Cycle.cycleGraph_edges_length (n : ℕ) :
    (Cycle.cycleGraph n).edges.length = n + 3 := by
  simp [Cycle.edges_length, Cycle.length_cycleGraph]

/-- Eulerian cycle edges are nodup. -/
lemma Cycle.cycleGraph_edges_nodup (n : ℕ) : (Cycle.cycleGraph n).edges.Nodup :=
  (Cycle.cycleGraph n).edges_nodup

/-- Bridgeless graphs are forests iff they have no edges. -/
theorem IsBridgeless.edgeFinset_eq_empty_iff_isAcyclic [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : IsBridgeless G) :
    G.edgeFinset = ∅ ↔ G.IsAcyclic := by
  constructor
  · intro he
    have : G = ⊥ := edgeFinset_eq_empty.mp he
    exact this ▸ isAcyclic_bot
  · exact fun hacyc ↦ edgeFinset_eq_empty_of_isBridgeless_of_isAcyclic G hacyc h

/-- Specialize: `C_{n+3}` has a nonempty edge set. -/
lemma cycleGraph_edgeFinset_ne_empty (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp (cycleGraph_edgeFinset_nonempty n)

/-- Third vertex on `Fin (n+3)` distinct from a given adjacent pair. -/
lemma exists_fin_ne_of_ne {n : ℕ} {u v : Fin (n + 3)} (_huv : u ≠ v) :
    ∃ w : Fin (n + 3), w ≠ u ∧ w ≠ v := by
  classical
  have hlt : ({u, v} : Finset (Fin (n + 3))).card < Fintype.card (Fin (n + 3)) := by
    have : ({u, v} : Finset _).card ≤ 2 := Finset.card_le_two
    simp only [Fintype.card_fin]
    omega
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨w, fun h ↦ by simp [h] at hw, fun h ↦ by simp [h] at hw⟩

/-- The length-2 path `v → w → u` in `K_{n+3}` is a path when vertices are pairwise distinct. -/
lemma completeGraph_path_two {n : ℕ} {u v w : Fin (n + 3)}
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    (Walk.cons (show (completeGraph (Fin (n + 3))).Adj v w from hvw)
      (Walk.cons (show (completeGraph (Fin (n + 3))).Adj w u from hwu) Walk.nil)).IsPath := by
  rw [Walk.cons_isPath_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    exact ⟨Walk.IsPath.nil, by simp [Walk.support_nil, hwu]⟩
  · simpa [Walk.support_cons, Walk.support_nil] using And.intro hvw huv.symm

/-- Triangle through three distinct vertices is a cycle in `K_{n+3}`. -/
lemma completeGraph_triangle_isCycle {n : ℕ} {u v w : Fin (n + 3)}
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    (Walk.cons (show (completeGraph (Fin (n + 3))).Adj u v from huv)
      (Walk.cons (show (completeGraph (Fin (n + 3))).Adj v w from hvw)
        (Walk.cons (show (completeGraph (Fin (n + 3))).Adj w u from hwu) Walk.nil))).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨completeGraph_path_two huv hvw hwu, ?_⟩
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false]
  refine not_or.mpr ⟨?_, ?_⟩
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨hu, _⟩ | ⟨hu, _⟩
    · exact huv hu
    · exact hwu hu.symm
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact hwu hu.symm
    · exact hvw hv

/-- Every edge of `K_{n+3}` lies on a triangle, so `K_{n+3}` is bridgeless. -/
theorem completeGraph_isBridgeless (n : ℕ) :
    IsBridgeless (completeGraph (Fin (n + 3))) := by
  classical
  refine IsBridgeless.of_forall_exists_cycle_mem_edges fun e he ↦ ?_
  revert he
  induction e using Sym2.inductionOn with
  | hf u v =>
    intro he
    have huv : u ≠ v := by
      have : ¬s(u, v).IsDiag := by simpa [mem_edgeSet] using he
      exact mt Sym2.mk_isDiag_iff.mpr this
    obtain ⟨w, hwu, hwv⟩ := exists_fin_ne_of_ne huv
    have hvw : v ≠ w := hwv.symm
    have hwu' : w ≠ u := hwu
    refine ⟨⟨u,
      Walk.cons (show (completeGraph (Fin (n + 3))).Adj u v from huv)
        (Walk.cons (show (completeGraph (Fin (n + 3))).Adj v w from hvw)
          (Walk.cons (show (completeGraph (Fin (n + 3))).Adj w u from hwu') Walk.nil)),
      completeGraph_triangle_isCycle huv hvw hwu'⟩, ?_⟩
    simp [Cycle.edges, Walk.edges_cons]

/-- For any `n ≥ 3`, `K_n` on `Fin n` is bridgeless. -/
theorem completeGraph_isBridgeless_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    IsBridgeless (completeGraph (Fin n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show (3 + k) = k + 3 from Nat.add_comm 3 k]
  exact completeGraph_isBridgeless k

/-- Bundled triangle `0-1-2-0` in `K_{n+3}`. -/
lemma fin_add3_zero_ne_one (n : ℕ) : (0 : Fin (n + 3)) ≠ 1 := by
  apply Fin.ne_of_val_ne
  have h0 : ((0 : Fin (n + 3)) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin (n + 3)) : ℕ) = 1 % (n + 3) := Fin.val_one' (n + 3)
  have : 1 % (n + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  omega

lemma fin_add3_one_ne_two (n : ℕ) : (1 : Fin (n + 3)) ≠ 2 := by
  apply Fin.ne_of_val_ne
  have h1 : ((1 : Fin (n + 3)) : ℕ) = 1 % (n + 3) := Fin.val_one' (n + 3)
  have h2 : ((2 : Fin (n + 3)) : ℕ) = 2 % (n + 3) := Fin.coe_ofNat_eq_mod (n + 3) 2
  have : 1 % (n + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  have : 2 % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  omega

lemma fin_add3_two_ne_zero (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  apply Fin.ne_of_val_ne
  have h2 : ((2 : Fin (n + 3)) : ℕ) = 2 % (n + 3) := Fin.coe_ofNat_eq_mod (n + 3) 2
  have h0 : ((0 : Fin (n + 3)) : ℕ) = 0 := rfl
  have : 2 % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Bundled triangle `0-1-2-0` in `K_{n+3}`. -/
def Cycle.completeGraph_triangle (n : ℕ) : Cycle (completeGraph (Fin (n + 3))) :=
  ⟨0,
    Walk.cons (show (completeGraph (Fin (n + 3))).Adj 0 1 from fin_add3_zero_ne_one n)
      (Walk.cons (show (completeGraph (Fin (n + 3))).Adj 1 2 from fin_add3_one_ne_two n)
        (Walk.cons (show (completeGraph (Fin (n + 3))).Adj 2 0 from fin_add3_two_ne_zero n)
          Walk.nil)),
    completeGraph_triangle_isCycle (fin_add3_zero_ne_one n) (fin_add3_one_ne_two n)
      (fin_add3_two_ne_zero n)⟩

@[simp]
lemma Cycle.length_completeGraph_triangle (n : ℕ) :
    (Cycle.completeGraph_triangle n).length = 3 := by
  simp [completeGraph_triangle, length, Walk.length_cons]

/-- `K_{n+3}` has an odd cycle (a triangle), hence `HasOddCycleWithChords _ 0`. -/
lemma hasOddCycleWithChords_completeGraph_zero (n : ℕ) :
    HasOddCycleWithChords (completeGraph (Fin (n + 3))) 0 :=
  ⟨Cycle.completeGraph_triangle n, by
    rw [Cycle.length_completeGraph_triangle]
    exact ⟨1, rfl⟩, bot_le⟩

/-- Same for any `K_n` with `n ≥ 3`. -/
lemma hasOddCycleWithChords_completeGraph_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    HasOddCycleWithChords (completeGraph (Fin n)) 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show (3 + k) = k + 3 from Nat.add_comm 3 k]
  exact hasOddCycleWithChords_completeGraph_zero k


end SimpleGraph
