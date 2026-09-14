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

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Cycle lengths and circumference

The cycle lengths and the longest cycle length of a graph.
-/

namespace SimpleGraph

/-- `G.cycleLengths` is the set of lengths of the cycles in `G`. -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

lemma mem_cycleLengths_iff {α : Type*} {G : SimpleGraph α} {m : ℕ} :
    m ∈ G.cycleLengths ↔ ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m :=
  Iff.rfl

/-- Every cycle length is at least `3`. -/
lemma three_le_of_mem_cycleLengths {α : Type*} {G : SimpleGraph α} {m : ℕ}
    (hm : m ∈ G.cycleLengths) : 3 ≤ m := by
  obtain ⟨a, w, hc, rfl⟩ := hm
  exact hc.three_le_length

/-- `G.oddCycleLengths` is the set of lengths of odd cycles in `G`. -/
def oddCycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

lemma mem_oddCycleLengths_iff {α : Type*} {G : SimpleGraph α} {m : ℕ} :
    m ∈ G.oddCycleLengths ↔ m ∈ G.cycleLengths ∧ Odd m :=
  Iff.rfl

/-- Lengths strictly below `3` are never cycle lengths. -/
lemma not_mem_cycleLengths_of_lt_three {α : Type*} {G : SimpleGraph α} {m : ℕ}
    (hm : m < 3) : m ∉ G.cycleLengths :=
  fun h ↦ (three_le_of_mem_cycleLengths h).not_gt hm

lemma oddCycleLengths_subset_cycleLengths {α : Type*} (G : SimpleGraph α) :
    G.oddCycleLengths ⊆ G.cycleLengths :=
  fun _ ↦ And.left

/-- Acyclic graphs have no cycle lengths. -/
lemma IsAcyclic.cycleLengths_eq_empty {α : Type*} {G : SimpleGraph α} (h : G.IsAcyclic) :
    G.cycleLengths = ∅ := by
  ext m
  simp only [Set.mem_empty_iff_false, iff_false, mem_cycleLengths_iff]
  rintro ⟨_a, w, hc, rfl⟩
  exact h w hc

/-- The empty graph has no cycle lengths. -/
@[simp]
lemma cycleLengths_bot {α : Type*} : (⊥ : SimpleGraph α).cycleLengths = ∅ :=
  IsAcyclic.cycleLengths_eq_empty isAcyclic_bot

/-- Cycle lengths are monotone in the edge set. -/
lemma cycleLengths_mono {α : Type*} {G H : SimpleGraph α} (h : G ≤ H) :
    G.cycleLengths ⊆ H.cycleLengths := by
  intro m hm
  obtain ⟨a, w, hc, rfl⟩ := hm
  refine ⟨a, w.mapLe h, (Walk.isCycle_mapLe h).mpr hc, ?_⟩
  simp

/-- Odd cycle lengths are monotone in the edge set. -/
lemma oddCycleLengths_mono {α : Type*} {G H : SimpleGraph α} (h : G ≤ H) :
    G.oddCycleLengths ⊆ H.oddCycleLengths := by
  intro m hm
  exact ⟨cycleLengths_mono h hm.1, hm.2⟩

variable {α : Type*} [Fintype α]

/-- A cycle uses at most `#α` vertices, so its length is `≤ Fintype.card α`. -/
lemma mem_cycleLengths_le_card {G : SimpleGraph α} {m : ℕ}
    (hm : m ∈ G.cycleLengths) : m ≤ Fintype.card α := by
  obtain ⟨_a, w, hc, rfl⟩ := hm
  have hnodup := hc.nodup_dropLast_support
  have hlen : w.support.dropLast.length = w.length := by
    rw [List.length_dropLast, Walk.length_support]
    omega
  exact hlen ▸ hnodup.length_le_card

lemma bddAbove_cycleLengths (G : SimpleGraph α) : BddAbove G.cycleLengths :=
  ⟨Fintype.card α, fun _ hm ↦ mem_cycleLengths_le_card hm⟩

/-- `circumference G` is the length of the longest cycle in `G`.
    It is `0` when `G` is acyclic. -/
noncomputable def circumference (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup G.cycleLengths

lemma le_circumference_of_mem_cycleLengths {G : SimpleGraph α} [DecidableRel G.Adj] {m : ℕ}
    (hm : m ∈ G.cycleLengths) : m ≤ G.circumference :=
  le_csSup (bddAbove_cycleLengths G) hm

omit [Fintype α] in
lemma circumference_eq_zero_of_cycleLengths_eq_empty {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : G.cycleLengths = ∅) : G.circumference = 0 := by
  simp [circumference, h]

omit [Fintype α] in
lemma IsAcyclic.circumference_eq_zero {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : G.IsAcyclic) : G.circumference = 0 :=
  circumference_eq_zero_of_cycleLengths_eq_empty h.cycleLengths_eq_empty

/-- Circumference is at most the number of vertices. -/
lemma circumference_le_card (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.circumference ≤ Fintype.card α := by
  by_cases h : G.cycleLengths.Nonempty
  · exact csSup_le h fun m hm ↦ mem_cycleLengths_le_card hm
  · have hempty : G.cycleLengths = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [circumference_eq_zero_of_cycleLengths_eq_empty hempty]

/-- If there is any cycle, the circumference is at least `3`. -/
lemma three_le_circumference_of_nonempty {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : G.cycleLengths.Nonempty) : 3 ≤ G.circumference := by
  obtain ⟨m, hm⟩ := h
  exact (three_le_of_mem_cycleLengths hm).trans (le_circumference_of_mem_cycleLengths hm)

/-- Circumference vanishes if and only if there are no cycles. -/
lemma circumference_eq_zero_iff {G : SimpleGraph α} [DecidableRel G.Adj] :
    G.circumference = 0 ↔ G.cycleLengths = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hne' : G.cycleLengths.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have : 3 ≤ G.circumference := three_le_circumference_of_nonempty hne'
    omega
  · exact circumference_eq_zero_of_cycleLengths_eq_empty

omit [Fintype α] in
/-- The empty graph has circumference `0`. -/
lemma circumference_bot [DecidableEq α] : (⊥ : SimpleGraph α).circumference = 0 :=
  circumference_eq_zero_of_cycleLengths_eq_empty cycleLengths_bot

/-- Circumference is monotone in the edge set. -/
lemma circumference_mono {G H : SimpleGraph α} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ≤ H) : G.circumference ≤ H.circumference := by
  by_cases hg : G.cycleLengths.Nonempty
  · refine csSup_le hg fun m hm ↦ le_circumference_of_mem_cycleLengths (cycleLengths_mono h hm)
  · have : G.cycleLengths = ∅ := Set.not_nonempty_iff_eq_empty.mp hg
    simp [circumference_eq_zero_of_cycleLengths_eq_empty this]


/-- The canonical Eulerian cycle of `cycleGraph (n + 3)` witnesses length `n + 3`. -/
lemma mem_cycleLengths_cycleGraph (n : ℕ) :
    n + 3 ∈ (cycleGraph (n + 3)).cycleLengths :=
  ⟨0, cycleGraph.cycle n, cycleGraph.isCycle_cycle, cycleGraph.length_cycle⟩

/-- Consequently `cycleGraph (n + 3)` is not acyclic. -/
lemma cycleGraph_not_isAcyclic (n : ℕ) : ¬ (cycleGraph (n + 3)).IsAcyclic := by
  intro h
  have hempty := h.cycleLengths_eq_empty
  have hmem := mem_cycleLengths_cycleGraph n
  rw [hempty] at hmem
  exact hmem

/-- Odd-length cycle graphs contribute their length to `oddCycleLengths`. -/
lemma mem_oddCycleLengths_cycleGraph {n : ℕ} (h : Odd (n + 3)) :
    n + 3 ∈ (cycleGraph (n + 3)).oddCycleLengths :=
  ⟨mem_cycleLengths_cycleGraph n, h⟩

/-- The circumference of `cycleGraph (n + 3)` is exactly `n + 3`. -/
theorem circumference_cycleGraph (n : ℕ) :
    (cycleGraph (n + 3)).circumference = n + 3 := by
  refine le_antisymm ?_ (le_circumference_of_mem_cycleLengths (mem_cycleLengths_cycleGraph n))
  -- `circumference ≤ #Fin (n+3) = n+3`
  simpa using circumference_le_card (cycleGraph (n + 3))



/-- If a cycle of length `#α` exists, the circumference attains the absolute upper bound. -/
lemma circumference_eq_card_of_mem_cycleLengths {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : Fintype.card α ∈ G.cycleLengths) : G.circumference = Fintype.card α :=
  le_antisymm (circumference_le_card G) (le_circumference_of_mem_cycleLengths h)

/-- `cycleGraph (n + 3)` embeds into the complete graph on the same vertex set. -/
lemma cycleGraph_le_completeGraph (n : ℕ) :
    cycleGraph (n + 3) ≤ (⊤ : SimpleGraph (Fin (n + 3))) :=
  le_top

/-- Hence the complete graph on `n + 3` vertices has circumference at least `n + 3`. -/
lemma n_add_three_le_circumference_completeGraph (n : ℕ) :
    n + 3 ≤ (⊤ : SimpleGraph (Fin (n + 3))).circumference := by
  have := circumference_mono (cycleGraph_le_completeGraph n)
  simpa [circumference_cycleGraph n] using this

/-- The complete graph on `Fin (n + 3)` has circumference exactly `n + 3`. -/
theorem circumference_completeGraph_fin (n : ℕ) :
    (⊤ : SimpleGraph (Fin (n + 3))).circumference = n + 3 :=
  le_antisymm (by simpa using circumference_le_card (⊤ : SimpleGraph (Fin (n + 3))))
    (n_add_three_le_circumference_completeGraph n)

/-- Same statement with `completeGraph` notation. -/
theorem circumference_completeGraph (n : ℕ) :
    (completeGraph (Fin (n + 3))).circumference = n + 3 :=
  circumference_completeGraph_fin n


/-- For any `n ≥ 3`, the complete graph on `Fin n` has circumference `n`. -/
theorem circumference_completeGraph_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (completeGraph (Fin n)).circumference = n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, show (3 + k) = k + 3 from Nat.add_comm 3 k]
  exact circumference_completeGraph k

/-- Hence `K_n` on `Fin n` (`n ≥ 3`) is not a forest. -/
lemma completeGraph_fin_not_isAcyclic {n : ℕ} (hn : 3 ≤ n) :
    ¬ (completeGraph (Fin n)).IsAcyclic := by
  intro h
  have hz : (completeGraph (Fin n)).circumference = 0 := h.circumference_eq_zero
  have hpos : (completeGraph (Fin n)).circumference = n :=
    circumference_completeGraph_of_three_le hn
  omega

/-- When `n + 3` is odd, that length lies in `oddCycleLengths` of `K_{n+3}`. -/
lemma mem_oddCycleLengths_completeGraph_fin {n : ℕ} (h : Odd (n + 3)) :
    n + 3 ∈ (completeGraph (Fin (n + 3))).oddCycleLengths :=
  oddCycleLengths_mono (cycleGraph_le_completeGraph n) (mem_oddCycleLengths_cycleGraph h)

/-- Same with `⊤` notation. -/
lemma circumference_top_fin_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).circumference = n := by
  simpa [completeGraph] using circumference_completeGraph_of_three_le hn



/-- If `#α < 3` then `G` has no cycle of length `≥ 3`, so the circumference vanishes. -/
lemma circumference_eq_zero_of_card_lt_three {G : SimpleGraph α} [DecidableRel G.Adj]
    (h : Fintype.card α < 3) : G.circumference = 0 := by
  by_contra hne
  have hcycles : G.cycleLengths.Nonempty := by
    have : G.cycleLengths ≠ ∅ := fun hempty =>
      hne (circumference_eq_zero_of_cycleLengths_eq_empty hempty)
    exact Set.nonempty_iff_ne_empty.mpr this
  have h3 : 3 ≤ G.circumference := three_le_circumference_of_nonempty hcycles
  have hle : G.circumference ≤ Fintype.card α := circumference_le_card G
  omega

/-- For `n < 3`, `K_n` on `Fin n` has circumference `0`. -/
lemma circumference_completeGraph_of_lt_three {n : ℕ} (hn : n < 3) :
    (completeGraph (Fin n)).circumference = 0 :=
  circumference_eq_zero_of_card_lt_three (by simpa)

/-- Combined: circumference of `K_n` on `Fin n` is `n` if `n ≥ 3`, else `0`. -/
theorem circumference_completeGraph_fin_eq {n : ℕ} :
    (completeGraph (Fin n)).circumference = if 3 ≤ n then n else 0 := by
  split_ifs with hn
  · exact circumference_completeGraph_of_three_le hn
  · exact circumference_completeGraph_of_lt_three (lt_of_not_ge hn)


end SimpleGraph
