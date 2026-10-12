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

public import FormalConjecturesUtil

/-!
# The Alon-Tarsi short cycle cover conjecture

*References:*
- [AlTa85] Alon, N. and Tarsi, M., Covering multigraphs by simple circuits.
  SIAM J. Algebraic Discrete Methods (1985), 345--350.
- [arxiv/2607.06396](https://arxiv.org/abs/2607.06396)
  **Some new results on Sylvester colorings of cubic graphs**
  by *Luca Ferrarini, Vahan Mkrtchyan*, where this is Conjecture 4.

This file states the finite simple-graph specialization of the source, which allows parallel edges.

Every bridgeless simple graph has a list of cycles covering every edge whose lengths sum to at most
$\frac{7}{5}|E|$.
-/

@[expose] public section

open Finset SimpleGraph

namespace Arxiv.«2607.06396»

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `C` covers `G`: every edge of `G` lies on at least one cycle of `C`. -/
def IsCycleCover (G : SimpleGraph V) [DecidableRel G.Adj] (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeFinset, ∃ c ∈ C, e ∈ c.edges

/-- The total length of a family of cycles. -/
def totalLength {G : SimpleGraph V} (C : Multiset (Cycle G)) : ℕ := (C.map SimpleGraph.Cycle.length).sum

omit [Fintype V] [DecidableEq V] in
/-- The empty family has total length zero. -/
@[simp, category API, AMS 5]
theorem totalLength_zero {G : SimpleGraph V} : totalLength (0 : Multiset (Cycle G)) = 0 := by
  simp [totalLength]

omit [Fintype V] [DecidableEq V] in
/-- Joining cycle families adds their total lengths, counting repetitions. -/
@[simp, category API, AMS 5]
theorem totalLength_add {G : SimpleGraph V} (C D : Multiset (Cycle G)) :
    totalLength (C + D) = totalLength C + totalLength D := by
  simp [totalLength]

omit [DecidableEq V] in
/-- The empty family covers exactly the graphs with no edges. -/
@[simp, category API, AMS 5]
theorem isCycleCover_zero_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsCycleCover G 0 ↔ G.edgeFinset = ∅ := by
  simp [IsCycleCover, Finset.eq_empty_iff_forall_notMem]

omit [DecidableEq V] in
/-- Clearing the rational denominator gives an equivalent natural-number bound. -/
@[category API, AMS 5]
theorem totalLength_le_seven_fifths_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) :
    (totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset ↔
      5 * totalLength C ≤ 7 * #G.edgeFinset := by
  have h : (totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset ↔
      5 * (totalLength C : ℚ) ≤ 7 * (#G.edgeFinset : ℚ) := by
    constructor <;> intro h <;> linarith
  exact_mod_cast h

/--
**Conjecture 4 (Alon-Tarsi, 1985), simple-graph specialization.** Every bridgeless simple graph
has a list of cycles covering
every edge, with $\sum_{C} |E(C)| \leq \frac{7}{5}|E(G)|$.
-/
@[category research open, AMS 5]
theorem alon_tarsi_short_cycle_cover :
    answer(sorry) ↔ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsBridgeless →
      ∃ C : Multiset (Cycle G), IsCycleCover G C ∧
        (totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset := by
  sorry

omit [DecidableEq V] in
/-- The empty cover works when there are no edges, so the bound is attained with room to spare
on edgeless graphs. -/
@[category test, AMS 5]
theorem exists_cover_of_edgeFinset_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset = ∅) :
    ∃ C : Multiset (Cycle G), IsCycleCover G C ∧
      (totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset := by
  refine ⟨0, ?_, ?_⟩
  · intro e he
    rw [h] at he
    exact absurd he (Finset.notMem_empty e)
  · simp [totalLength, h]

omit [DecidableEq V] in
/-- Acyclic bridgeless graphs satisfy the conjecture, with the empty cover. In a forest every
edge is a bridge, so such a graph has no edges at all. -/
@[category test, AMS 5]
theorem exists_cover_of_isAcyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hbr : G.IsBridgeless) :
    ∃ C : Multiset (Cycle G), IsCycleCover G C ∧
      (totalLength C : ℚ) ≤ 7 / 5 * #G.edgeFinset :=
  exists_cover_of_edgeFinset_eq_empty G
    (G.edgeFinset_eq_empty_of_isBridgeless_of_isAcyclic hacyc hbr)

omit [Fintype V] [DecidableEq V] in
/-- A cycle has at least three edges, so any cover of a graph with an edge has total length at
least three. This is what makes the `7/5` bound a real constraint rather than a formality. -/
@[category API, AMS 5]
theorem three_le_length {G : SimpleGraph V} (c : Cycle G) : 3 ≤ c.length :=
  c.isCycle.three_le_length

end Arxiv.«2607.06396»
