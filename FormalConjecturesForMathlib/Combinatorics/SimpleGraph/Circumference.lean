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

end SimpleGraph
