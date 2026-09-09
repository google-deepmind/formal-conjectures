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
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite inputs for feedback sets and network design

Definitions follow Garey and Johnson, *Computers and Intractability* (1979),
GT7–GT8 (pp. 191–192), ND12 (pp. 208–209), ND22 (p. 211), and ND40 (p. 217).
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Graphs have explicit Boolean adjacency matrices. Integer costs and bounds use the
existing binary encodings. Feedback sets meet every directed simple cycle, including
two-cycles. Steiner trees use nonnegative weights and actual Mathlib trees; each
undirected edge contributes once. Routing uses an input-sized list of mutually
distinct terminal pairs, not a fixed number of pairs.

All decidability instances are finite exhaustive searches, with no efficiency claim.
-/

@[expose] public section

namespace SimpleGraph

/-- Finite tree recognition using connectivity and the exact edge count. -/
instance decidableIsTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable G.IsTree :=
  decidable_of_iff (G.Connected ∧ G.edgeFinset.card + 1 = Fintype.card V) (by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, edgeFinset_card])

end SimpleGraph

namespace Computability.NetworkProblems

open MatrixGraph

/-- A directed simple cycle described by its cyclically ordered, distinct vertices. -/
def DirectedCycle (a : Code) {m : ℕ} (c : Fin m → Fin a.length) : Prop :=
  2 ≤ m ∧ Function.Injective c ∧ ∀ i, entry a (c i) (c (next i)) = true

instance (a : Code) {m : ℕ} (c : Fin m → Fin a.length) :
    Decidable (DirectedCycle a c) := by
  unfold DirectedCycle Function.Injective
  infer_instance

theorem DirectedCycle.length_le {a : Code} {m : ℕ} {c : Fin m → Fin a.length}
    (h : DirectedCycle a c) : m ≤ a.length := by
  simpa using Fintype.card_le_of_injective c h.2.1

/-- Every simple directed cycle meets the chosen vertex set. -/
def HitsVertexCycles (a : Code) (s : Finset (Fin a.length)) : Prop :=
  ∀ m : Fin (a.length + 1), ∀ c : Fin m.val → Fin a.length,
    DirectedCycle a c → ∃ i, c i ∈ s

instance (a : Code) (s : Finset (Fin a.length)) : Decidable (HitsVertexCycles a s) := by
  unfold HitsVertexCycles
  infer_instance

/-- The finite bound loses no directed simple cycles. -/
theorem hitsVertexCycles_iff (a : Code) (s : Finset (Fin a.length)) :
    HitsVertexCycles a s ↔
      ∀ (m : ℕ) (c : Fin m → Fin a.length), DirectedCycle a c → ∃ i, c i ∈ s := by
  constructor
  · intro h m c hc
    exact h ⟨m, Nat.lt_succ_of_le hc.length_le⟩ c hc
  · intro h m c hc
    exact h m.val c hc

/-- The actual directed arcs, with their orientations retained. -/
def arcs (a : Code) : Finset (Fin a.length × Fin a.length) :=
  Finset.univ.filter fun e ↦ entry a e.1 e.2 = true

def HitsArcCycles (a : Code) (s : Finset (Fin a.length × Fin a.length)) : Prop :=
  ∀ m : Fin (a.length + 1), ∀ c : Fin m.val → Fin a.length,
    DirectedCycle a c → ∃ i, (c i, c (next i)) ∈ s

instance (a : Code) (s : Finset (Fin a.length × Fin a.length)) :
    Decidable (HitsArcCycles a s) := by
  unfold HitsArcCycles
  infer_instance

theorem hitsArcCycles_iff (a : Code) (s : Finset (Fin a.length × Fin a.length)) :
    HitsArcCycles a s ↔ ∀ (m : ℕ) (c : Fin m → Fin a.length),
      DirectedCycle a c → ∃ i, (c i, c (next i)) ∈ s := by
  constructor
  · intro h m c hc
    exact h ⟨m, Nat.lt_succ_of_le hc.length_le⟩ c hc
  · intro h m c hc
    exact h m.val c hc

/-- GT7: delete at most a positive input bound of vertices to meet all directed cycles.
The source also requires the bound to be at most the number of vertices. -/
def FeedbackVertexSet (input : Code × ℕ) : Prop :=
  ValidDigraph input.1 ∧ 0 < input.2 ∧ input.2 ≤ input.1.length ∧
    ∃ s : Finset (Fin input.1.length), s.card ≤ input.2 ∧ HitsVertexCycles input.1 s

/-- GT8: delete at most a positive input bound of actual arcs to meet all directed cycles.
The source also requires the bound to be at most the number of arcs. -/
def FeedbackArcSet (input : Code × ℕ) : Prop :=
  ValidDigraph input.1 ∧ 0 < input.2 ∧ input.2 ≤ (arcs input.1).card ∧
    ∃ s : Finset (Fin input.1.length × Fin input.1.length),
      s ⊆ arcs input.1 ∧ s.card ≤ input.2 ∧ HitsArcCycles input.1 s

instance (input : Code × ℕ) : Decidable (FeedbackVertexSet input) := by
  unfold FeedbackVertexSet
  infer_instance

instance (input : Code × ℕ) : Decidable (FeedbackArcSet input) := by
  unfold FeedbackArcSet
  infer_instance

/-- Missing weights default to zero; the input predicates independently check dimensions. -/
def weight (w : List (List ℕ)) (i j : ℕ) : ℕ :=
  ((w[i]?.getD [])[j]?).getD 0

def WeightMatrix (w : List (List ℕ)) (n : ℕ) : Prop :=
  w.length = n ∧ (∀ row ∈ w, row.length = n) ∧
    ∀ i j : Fin n, weight w i.val j.val = weight w j.val i.val

instance (w : List (List ℕ)) (n : ℕ) : Decidable (WeightMatrix w n) := by
  unfold WeightMatrix
  infer_instance

/-- An undirected graph on the selected vertices, generated by selected ordered pairs. -/
def selectedGraph {n : ℕ} (s : Finset (Fin n)) (e : Finset (Fin n × Fin n)) :
    SimpleGraph s :=
  SimpleGraph.fromRel fun u v ↦ (u.val, v.val) ∈ e

instance {n : ℕ} (s : Finset (Fin n)) (e : Finset (Fin n × Fin n)) :
    DecidableRel (selectedGraph s e).Adj := by
  unfold selectedGraph SimpleGraph.fromRel
  infer_instance

/-- Canonical edge orientation excludes loops and duplicate reverse orientations. -/
def SelectedEdges (a : Code) (s : Finset (Fin a.length))
    (e : Finset (Fin a.length × Fin a.length)) : Prop :=
  ∀ p ∈ e, p.1 < p.2 ∧ p.1 ∈ s ∧ p.2 ∈ s ∧ entry a p.1 p.2 = true

instance (a : Code) (s : Finset (Fin a.length))
    (e : Finset (Fin a.length × Fin a.length)) : Decidable (SelectedEdges a s e) := by
  unfold SelectedEdges
  infer_instance

/-- Graph, symmetric nonnegative weight matrix, terminal mask, and positive budget. -/
abbrev SteinerInput := Code × (List (List ℕ) × (List Bool × ℕ))

/-- ND12: a nonempty tree containing all terminals, of total edge weight at most the budget.
A singleton is a tree of weight zero; an empty graph contains no tree. -/
def SteinerTree (input : SteinerInput) : Prop :=
  let a := input.1
  let w := input.2.1
  let terminals := input.2.2.1
  let budget := input.2.2.2
  ValidGraph a ∧ WeightMatrix w a.length ∧ terminals.length = a.length ∧ 0 < budget ∧
    ∃ s : Finset (Fin a.length), ∃ e : Finset (Fin a.length × Fin a.length),
      (∀ v, terminals[v.val]?.getD false = true → v ∈ s) ∧
      SelectedEdges a s e ∧ (selectedGraph s e).IsTree ∧
      (∑ p ∈ e, weight w p.1.val p.2.val) ≤ budget

instance (input : SteinerInput) : Decidable (SteinerTree input) := by
  unfold SteinerTree
  infer_instance

/-- Symmetric complete distance data, with zero diagonal and positive off-diagonal costs. -/
def TourMatrix (w : List (List ℕ)) : Prop :=
  WeightMatrix w w.length ∧
    (∀ i : Fin w.length, weight w i.val i.val = 0) ∧
    ∀ i j : Fin w.length, i ≠ j → 0 < weight w i.val j.val

instance (w : List (List ℕ)) : Decidable (TourMatrix w) := by
  unfold TourMatrix
  infer_instance

/-- A tour includes the return leg to its starting city. Empty and singleton tours cost zero. -/
def tourCost (w : List (List ℕ)) (order : Equiv.Perm (Fin w.length)) : ℕ :=
  ∑ i, weight w (order i).val (order (next i)).val

/-- ND22: a symmetric travelling-salesman tour within a positive budget.
No triangle inequality is assumed. Two-city tours pay for both directions. -/
def TravelingSalesman (input : List (List ℕ) × ℕ) : Prop :=
  TourMatrix input.1 ∧ 0 < input.2 ∧
    ∃ order : Equiv.Perm (Fin input.1.length), tourCost input.1 order ≤ input.2

instance (input : List (List ℕ) × ℕ) : Decidable (TravelingSalesman input) := by
  unfold TravelingSalesman
  infer_instance

/-- Every terminal occurs once, and all terminal names denote declared vertices. -/
def ValidPairs (n : ℕ) (pairs : List (ℕ × ℕ)) : Prop :=
  (pairs.flatMap fun p ↦ [p.1, p.2]).Nodup ∧
    ∀ p ∈ pairs, p.1 < n ∧ p.2 < n

instance (n : ℕ) (pairs : List (ℕ × ℕ)) : Decidable (ValidPairs n pairs) := by
  unfold ValidPairs
  infer_instance

/-- A path inside a chosen vertex region connecting the specified terminal names.
Mathlib reachability is equivalent to existence of a simple path. -/
def ConnectsIn (a : Code) (s : Finset (Fin a.length)) (pair : ℕ × ℕ) : Prop :=
  ∃ u v : s, u.val.val = pair.1 ∧ v.val.val = pair.2 ∧
    ((toGraph a).induce (s : Set (Fin a.length))).Reachable u v

instance (a : Code) (s : Finset (Fin a.length)) (pair : ℕ × ℕ) :
    Decidable (ConnectsIn a s pair) := by
  unfold ConnectsIn
  infer_instance

/-- The region formulation supplies actual simple paths, not just arbitrary walks. -/
theorem connectsIn_iff_exists_path (a : Code) (s : Finset (Fin a.length))
    (pair : ℕ × ℕ) : ConnectsIn a s pair ↔
      ∃ u v : s, u.val.val = pair.1 ∧ v.val.val = pair.2 ∧
        ∃ p : ((toGraph a).induce (s : Set (Fin a.length))).Walk u v, p.IsPath := by
  constructor
  · rintro ⟨u, v, hu, hv, hr⟩
    exact ⟨u, v, hu, hv, hr.exists_isPath⟩
  · rintro ⟨u, v, hu, hv, p, _⟩
    exact ⟨u, v, hu, hv, ⟨p⟩⟩

/-- ND40: simultaneous vertex-disjoint paths for an input-sized list of terminal pairs.
The disjoint regions enforce disjointness of entire paths, including their endpoints. -/
def DisjointConnectingPaths (input : Code × List (ℕ × ℕ)) : Prop :=
  let a := input.1
  let pairs := input.2
  ValidGraph a ∧ ValidPairs a.length pairs ∧
    ∃ regions : Fin pairs.length → Finset (Fin a.length),
      (∀ i j, i ≠ j → Disjoint (regions i) (regions j)) ∧
      ∀ i, ConnectsIn a (regions i) pairs[i.val]

instance (input : Code × List (ℕ × ℕ)) : Decidable (DisjointConnectingPaths input) := by
  unfold DisjointConnectingPaths
  infer_instance

end Computability.NetworkProblems
