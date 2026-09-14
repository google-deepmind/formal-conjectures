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

public meta import FormalConjecturesForMathlib.Computability.NetworkProblems
public import FormalConjecturesForMathlib.Computability.NetworkProblems
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Boundary and semantic tests for feedback sets and network design -/

@[expose] public section

namespace Computability.NetworkProblems.Test

open MatrixGraph BitstringEncoding

abbrev edge : Code := [[false, true], [true, false]]
abbrev arc : Code := [[false, true], [false, false]]
abbrev cycle : Code :=
  [[false, true, false], [false, false, true], [true, false, false]]
abbrev triangle : Code :=
  [[false, true, true], [true, false, true], [true, true, false]]
abbrev chain : Code :=
  [[false, true, false], [true, false, true], [false, true, false]]
abbrev twoEdges : Code :=
  [[false, true, false, false], [true, false, false, false],
   [false, false, false, true], [false, false, true, false]]
abbrev costs : List (List ℕ) := [[0, 2, 9], [2, 0, 3], [9, 3, 0]]

example : DirectedCycle edge (fun i : Fin 2 ↦ i) := by decide
example : ¬ DirectedCycle arc (fun i : Fin 2 ↦ i) := by decide
example : DirectedCycle cycle (fun i : Fin 3 ↦ i) := by decide
example : ¬ DirectedCycle cycle
    (fun i : Fin 3 ↦ ⟨2 - i.val, by change 2 - i.val < 3; omega⟩) := by decide
example : ¬ DirectedCycle edge (fun _ : Fin 3 ↦ 0) := by decide
example : ¬ DirectedCycle [[false]] (fun i : Fin 1 ↦ i) := by decide
example : HitsVertexCycles edge {0} := by decide
example : ¬ HitsVertexCycles edge ∅ := by decide
example : HitsVertexCycles arc ∅ := by decide
example : HitsArcCycles edge {(0, 1)} := by decide
example : ¬ HitsArcCycles edge {(0, 0)} := by decide
example : HitsArcCycles arc ∅ := by decide
example : (arcs arc).card = 1 := by decide
example : (arcs edge).card = 2 := by decide
example : (arcs cycle).card = 3 := by decide
example : ¬ FeedbackVertexSet ([], 1) := by decide
example : ¬ FeedbackVertexSet (edge, 0) := by decide
example : ¬ FeedbackVertexSet (edge, 3) := by decide
example : FeedbackVertexSet ([[false]], 1) := by decide
example : FeedbackVertexSet (arc, 1) := by decide
example : FeedbackVertexSet (edge, 1) := by decide
example : FeedbackVertexSet (cycle, 1) := by decide
example : ¬ FeedbackVertexSet (triangle, 1) := by decide
example : FeedbackVertexSet (triangle, 2) := by decide
example : ¬ FeedbackVertexSet (twoEdges, 1) := by decide
set_option maxRecDepth 2048 in
example : FeedbackVertexSet (twoEdges, 2) := by decide
example : ¬ FeedbackVertexSet ([[true]], 1) := by decide
example : ¬ FeedbackVertexSet ([[false, true]], 1) := by decide
example : ¬ FeedbackArcSet ([], 1) := by decide
example : ¬ FeedbackArcSet ([[false]], 1) := by decide
example : ¬ FeedbackArcSet (edge, 0) := by decide
example : ¬ FeedbackArcSet (arc, 2) := by decide
example : FeedbackArcSet (arc, 1) := by decide
example : FeedbackArcSet (edge, 1) := by decide
example : FeedbackArcSet (cycle, 1) := by decide
example : ¬ FeedbackArcSet ([[true]], 1) := by decide

example : WeightMatrix costs 3 := by decide
example : ¬ WeightMatrix costs 2 := by decide
example : ¬ WeightMatrix [[0, 1], [2, 0]] 2 := by decide
example : ¬ WeightMatrix [[0], [1, 0]] 2 := by decide
example : SelectedEdges edge {0, 1} {(0, 1)} := by decide
example : ¬ SelectedEdges edge {0, 1} {(1, 0)} := by decide
example : ¬ SelectedEdges edge {0, 1} {(0, 1), (1, 0)} := by decide
example : ¬ SelectedEdges edge {0} {(0, 1)} := by decide
example : ¬ SelectedEdges edge {0} {(0, 0)} := by decide
example : (selectedGraph ({0, 1} : Finset (Fin 2)) {(0, 1)}).IsTree := by decide
example : ¬ (selectedGraph ({0, 1} : Finset (Fin 2)) ∅).IsTree := by decide
example : ¬ SteinerTree ([], [], [], 1) := by decide
example : SteinerTree ([[false]], [[0]], [false], 1) := by decide
example : SteinerTree (edge, [[0, 2], [2, 0]], [true, true], 2) := by decide
example : ¬ SteinerTree (edge, [[0, 2], [2, 0]], [true, true], 1) := by decide
example : SteinerTree (edge, [[0, 0], [0, 0]], [true, true], 1) := by decide
example : ¬ SteinerTree (edge, [[0, 2], [2, 0]], [true], 2) := by decide
example : ¬ SteinerTree (edge, [[0, 2], [2, 0]], [true, true], 0) := by decide
example : ¬ (selectedGraph ({0, 1, 2} : Finset (Fin 3))
    {(0, 1), (0, 2), (1, 2)}).IsTree := by decide
set_option maxRecDepth 8192 in
example : SteinerTree (chain, costs, [true, false, true], 5) := by decide
set_option maxRecDepth 8192 in
example : ¬ SteinerTree (chain, costs, [true, false, true], 4) := by decide
set_option maxRecDepth 8192 in
example : SteinerTree (triangle, costs, [true, true, true], 5) := by decide
set_option maxRecDepth 8192 in
example : ¬ SteinerTree (triangle, costs, [true, true, true], 4) := by decide

example : TourMatrix costs := by decide
example : TourMatrix [] := by decide
example : ¬ TourMatrix [[1]] := by decide
example : ¬ TourMatrix [[0, 0], [0, 0]] := by decide
example : tourCost costs (Equiv.refl _) = 14 := by decide
example : TravelingSalesman (costs, 14) := by decide
example : ¬ TravelingSalesman (costs, 13) := by decide
example : TravelingSalesman ([[0, 3], [3, 0]], 6) := by decide
example : ¬ TravelingSalesman ([[0, 3], [3, 0]], 5) := by decide
example : TravelingSalesman ([[0]], 1) := by decide
example : TravelingSalesman ([], 1) := by decide
example : ¬ TravelingSalesman (costs, 0) := by decide

example : ValidPairs 4 [(0, 1), (2, 3)] := by decide
example : ¬ ValidPairs 4 [(0, 1), (1, 3)] := by decide
example : ¬ ValidPairs 4 [(0, 1), (1, 0)] := by decide
example : ¬ ValidPairs 4 [(0, 0)] := by decide
example : ¬ ValidPairs 4 [(0, 4)] := by decide
example : ConnectsIn chain {0, 1, 2} (0, 2) := by decide
example : ¬ ConnectsIn chain {0, 2} (0, 2) := by decide
example : DisjointConnectingPaths ([], []) := by decide
example : DisjointConnectingPaths (edge, [(0, 1)]) := by decide
example : ¬ DisjointConnectingPaths (edge, [(0, 2)]) := by decide
example : ¬ DisjointConnectingPaths (edge, [(0, 1), (0, 1)]) := by decide
example : ¬ DisjointConnectingPaths ([[true]], []) := by decide
set_option maxRecDepth 2048 in
example : DisjointConnectingPaths (twoEdges, [(0, 1), (2, 3)]) := by decide
set_option maxRecDepth 2048 in
example : ¬ DisjointConnectingPaths (twoEdges, [(0, 2), (1, 3)]) := by decide

example : bitDecode (bitEncode (costs, 14)) = some (costs, 14) :=
  bitDecode_bitEncode _
example : bitDecode (bitEncode ((edge, [(0, 1)]) : Code × List (ℕ × ℕ))) =
    some ((edge, [(0, 1)]) : Code × List (ℕ × ℕ)) := bitDecode_bitEncode _
example : bitDecode (bitEncode ((edge, [[0, 2], [2, 0]], [true, true], 2) : SteinerInput)) =
    some ((edge, [[0, 2], [2, 0]], [true, true], 2) : SteinerInput) := bitDecode_bitEncode _

theorem nonvacuous_machine_interface :
    ComplexityTheory.HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (FeedbackArcSet (cycle, 1)),
  decide (TravelingSalesman (costs, 13)), decide (TravelingSalesman (costs, 14)))

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (DisjointConnectingPaths (twoEdges, [(0, 1), (2, 3)])),
  decide (DisjointConnectingPaths (twoEdges, [(0, 2), (1, 3)])),
  decide (SteinerTree (chain, costs, [true, false, true], 5)))

end Computability.NetworkProblems.Test
