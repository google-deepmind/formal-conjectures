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

public import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Red/blue exact perfect matching

Two explicit matrices encode the graph and its red-edge subset. They must have
the same dimension, be square, symmetric and loopless, and every red edge must
be a graph edge. Other graph edges are blue. Malformed inputs are rejected.

A perfect matching is represented by the involution sending each vertex to its
unique mate. The smaller endpoint counts each red edge exactly once. The
connection to Mathlib's perfect-matching subgraphs is proved below.

Source: El Maalouly, *Exact Matching: Algorithms and Related Problems*,
STACS 2023, §1, pp. 29:1–29:3, https://doi.org/10.4230/LIPIcs.STACS.2023.29.
The target integer is binary, and equality is exact, not an upper bound.
-/

@[expose] public section

namespace Computability.MatrixGraph

/-- Matrix lookup at natural-number coordinates. -/
def entryAt (a : Code) (i j : ℕ) : Bool :=
  ((a[i]?.getD [])[j]?).getD false

/-- An undirected graph with a consistently encoded subset of red edges. -/
def ValidColoredGraph (a red : Code) : Prop :=
  ValidGraph a ∧ ValidGraph red ∧ red.length = a.length ∧
    ∀ i j : Fin a.length, entryAt red i.val j.val = true → entry a i j = true

instance (a red : Code) : Decidable (ValidColoredGraph a red) := by
  unfold ValidColoredGraph
  infer_instance

/-- Every vertex has a reciprocal mate along an edge. Looplessness rules out fixed points. -/
def IsMate (a : Code) (mate : Fin a.length → Fin a.length) : Prop :=
  Function.Involutive mate ∧ ∀ i, entry a i (mate i) = true

instance (a : Code) (mate : Fin a.length → Fin a.length) : Decidable (IsMate a mate) := by
  unfold IsMate Function.Involutive
  infer_instance

/-- Red matching edges are counted at their smaller endpoint, not at both endpoints. -/
def redCount (a red : Code) (mate : Fin a.length → Fin a.length) : ℕ :=
  (Finset.univ.filter fun i => i < mate i ∧ entryAt red i.val (mate i).val = true).card

/-- General-graph exact matching. Negative targets and malformed matrices are rejected. -/
def ExactMatching (input : Code × Code × ℤ) : Prop :=
  ValidColoredGraph input.1 input.2.1 ∧
    ∃ mate : Fin input.1.length → Fin input.1.length,
      IsMate input.1 mate ∧ (redCount input.1 input.2.1 mate : ℤ) = input.2.2

instance (input : Code × Code × ℤ) : Decidable (ExactMatching input) := by
  unfold ExactMatching
  infer_instance

/-- The actual spanning subgraph specified by the mate involution. -/
def IsMate.toSubgraph {a : Code} {mate : Fin a.length → Fin a.length}
    (h : IsMate a mate) (ha : ValidGraph a) : (toGraph a).Subgraph where
  verts := Set.univ
  Adj i j := mate i = j
  adj_sub := by
    intro i j hij
    rw [← hij]
    exact (toGraph_adj ha i (mate i)).mpr (h.2 i)
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro i j hij
    rw [← hij, h.1 i]⟩

theorem IsMate.isPerfectMatching {a : Code} {mate : Fin a.length → Fin a.length}
    (h : IsMate a mate) (ha : ValidGraph a) :
    (h.toSubgraph ha).IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro i
  exact ⟨mate i, rfl, fun j hj => Eq.symm hj⟩

/-- Every Mathlib perfect matching also has a mate-involution representation. -/
theorem exists_isMate_iff {a : Code} (ha : ValidGraph a) :
    (∃ mate, IsMate a mate) ↔ ∃ M : (toGraph a).Subgraph, M.IsPerfectMatching := by
  classical
  constructor
  · rintro ⟨mate, hm⟩
    exact ⟨hm.toSubgraph ha, hm.isPerfectMatching ha⟩
  · rintro ⟨M, hM⟩
    have hm := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
    let mate := fun i => Classical.choose (ExistsUnique.exists (hm i))
    have hedge (i) : M.Adj i (mate i) :=
      Classical.choose_spec (ExistsUnique.exists (hm i))
    refine ⟨mate, ?_, ?_⟩
    · intro i
      exact (hm (mate i)).unique (hedge (mate i)) (M.symm.symm _ _ (hedge i))
    · intro i
      exact (toGraph_adj ha i (mate i)).mp (M.adj_sub (hedge i))

theorem ExactMatching.even_vertices {input : Code × Code × ℤ}
    (h : ExactMatching input) : Even input.1.length := by
  obtain ⟨hv, mate, hm, _⟩ := h
  simpa using (hm.isPerfectMatching hv.1).even_card

theorem ExactMatching.nonneg_target {input : Code × Code × ℤ}
    (h : ExactMatching input) : 0 ≤ input.2.2 := by
  obtain ⟨_, mate, _, hk⟩ := h
  rw [← hk]
  exact Int.natCast_nonneg _

end Computability.MatrixGraph
