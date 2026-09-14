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

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `circumference G` is the length of the longest cycle in `G`.
    It is `0` when `G` is acyclic. -/
noncomputable def circumference (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup G.cycleLengths

end SimpleGraph
