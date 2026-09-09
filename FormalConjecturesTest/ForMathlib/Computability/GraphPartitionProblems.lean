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
import FormalConjecturesForMathlib.Computability.DecisionProblems
import FormalConjecturesForMathlib.Computability.GraphPartitionProblems

/-! # Boundary and semantic tests for graph partition problems -/

namespace Computability.GraphPartitionProblems.Test

open MatrixGraph NetworkProblems BitstringEncoding

abbrev edge : Code := [[false, true], [true, false]]
abbrev isolated : Code := [[false, false], [false, false]]
abbrev triangle : Code :=
  [[false, true, true], [true, false, true], [true, true, false]]
abbrev chain : Code :=
  [[false, true, false], [true, false, true], [false, true, false]]
abbrev square : Code :=
  [[false, false, true, true], [false, false, true, true],
   [true, true, false, false], [true, true, false, false]]
abbrev star : Code :=
  [[false, true, true, true], [true, false, false, false],
   [true, false, false, false], [true, false, false, false]]
abbrev twoTriangles : Code :=
  [[false, true, true, false, false, false], [true, false, true, false, false, false],
   [true, true, false, false, false, false], [false, false, false, false, true, true],
   [false, false, false, true, false, true], [false, false, false, true, true, false]]
abbrev costs : List (List ℕ) := [[0, 5], [5, 0]]

def partitionBy {n : ℕ} (label : Fin n → ℕ) : Finpartition (Finset.univ : Finset (Fin n)) := by
  letI : DecidableRel (Setoid.ker label).r := fun i j ↦
    inferInstanceAs (Decidable (label i = label j))
  exact Finpartition.ofSetoid (Setoid.ker label)

example : ¬ CliquePartition ([], 1) := by decide
example : ¬ CliquePartition (edge, 0) := by decide
example : ¬ CliquePartition (edge, 3) := by decide
example : ¬ CliquePartition ([[true]], 1) := by decide
example : ¬ CliquePartition ([[false, true], [false, false]], 1) := by decide
example : ¬ CliquePartition ([[false], [false]], 1) := by decide
example : CliquePartition ([[false]], 1) := by decide
example : CliquePartition (edge, 1) := by decide
example : CliquePartition (edge, 2) := by decide
example : ¬ CliquePartition (isolated, 1) := by decide
example : CliquePartition (isolated, 2) := by decide
example : CliquePartition (triangle, 1) := by
  refine ⟨by decide, by decide, by decide, ⊤, ?_⟩
  decide
example : CliquePartition (chain, 2) := by
  refine ⟨by decide, by decide, by decide,
    partitionBy (fun i : Fin 3 ↦ i.val / 2), ?_⟩
  decide

example : ¬ TrianglePartition [] := by decide
example : ¬ TrianglePartition [[false]] := by decide
example : ¬ TrianglePartition edge := by decide
example : ¬ TrianglePartition [[false], [false], [false]] := by decide
example : TrianglePartition triangle := by
  refine ⟨by decide, by decide, by decide, ⊤, ?_⟩
  decide
example : TrianglePartition twoTriangles := by
  refine ⟨by decide, by decide, by decide,
    partitionBy (fun i : Fin 6 ↦ i.val / 3), ?_⟩
  decide
set_option maxRecDepth 4096 in
example : ¬ TrianglePartition chain := by decide
example : (partitionBy (fun i : Fin 6 ↦ i.val / 3)).parts.card = 2 :=
  by decide
example (p : VertexPartition twoTriangles) (h : ∀ s ∈ p.parts, s.card = 3) :
    p.parts.card = 2 := by
  have := triangle_parts_card p h
  change 3 * p.parts.card = 6 at this
  omega

example : ¬ BalancedBiclique ([], 1) := by decide
example : ¬ BalancedBiclique (edge, 0) := by decide
example : ¬ BalancedBiclique (edge, 3) := by decide
example : ¬ BalancedBiclique ([[false]], 1) := by decide
example : BalancedBiclique (edge, 1) := by decide
example : ¬ BalancedBiclique (edge, 2) := by decide
example : ¬ BalancedBiclique (isolated, 1) := by decide
-- A triangle has a K₁,₁ subgraph but is not a bipartite input.
example : ¬ BalancedBiclique (triangle, 1) := by decide
example : ¬ BalancedBiclique ([[false, true], [false, false]], 1) := by decide
example : BalancedBiclique (square, 2) := by decide
-- A K₁,₃ is not a K₂,₂, despite having four vertices.
example : ¬ BalancedBiclique (star, 2) := by decide

example : crossingEdges edge (fun i ↦ i.val) = {(0, 1)} := by decide
example : crossingEdges edge (fun _ ↦ false) = ∅ := by decide
example : crossingWeight edge costs (fun i ↦ i.val) = 5 := by decide
example : crossingWeight edge costs (fun _ ↦ false) = 0 := by decide
example : crossingWeight isolated costs (fun i ↦ i.val) = 0 := by decide
example : crossingWeight edge [[99, 5], [5, 88]] (fun i ↦ i.val) = 5 := by decide
example : crossingWeight edge costs (fun i ↦ 1 - i.val) = 5 := by decide
example : ¬ ((1, 0) : Fin 2 × Fin 2) ∈ crossingEdges edge (fun i ↦ i.val) := by decide
example : crossingWeight square
    [[0, 0, 2, 3], [0, 0, 5, 7], [2, 5, 0, 0], [3, 7, 0, 0]]
    (fun i ↦ i.val / 2) = 17 := by decide

example : WeightedPartition ([], [], [], 1, 1) := by decide
example : ¬ WeightedPartition ([], [], [], 0, 1) := by decide
example : ¬ WeightedPartition ([], [], [], 1, 0) := by decide
example : WeightedPartition ([[false]], [2], [[0]], 2, 1) := by decide
example : ¬ WeightedPartition ([[false]], [2], [[0]], 1, 1) := by decide
example : ¬ WeightedPartition ([[false]], [0], [[0]], 1, 1) := by decide
example : ¬ WeightedPartition (edge, [1], costs, 2, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 1, 1], costs, 2, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 1], [[0]], 2, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 1], [[0, 5], [4, 0]], 2, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 1], [[0, 0], [0, 0]], 2, 5) := by decide
example : WeightedPartition (isolated, [1, 1], [[0, 0], [0, 0]], 1, 1) := by decide
example : WeightedPartition (edge, [1, 1], costs, 2, 1) := by decide
example : WeightedPartition (edge, [1, 1], costs, 1, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 1], costs, 1, 4) := by decide
example : WeightedPartition (edge, [1, 2], costs, 2, 5) := by decide
example : ¬ WeightedPartition (edge, [1, 2], costs, 2, 4) := by decide
example : WeightedPartition (edge, [1, 2], costs, 3, 1) := by decide
example : WeightedPartition (isolated, [1, 1], [[9, 99], [99, 8]], 1, 1) := by decide
example : ¬ WeightedPartition ([[true]], [1], [[1]], 1, 1) := by decide

example : ¬ BoundedCut ([], [], (0, 1), (1, 1)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 1), (0, 5)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 1), (3, 5)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 1), (1, 0)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 2), (1, 5)) := by decide
example : ¬ BoundedCut (edge, costs, (2, 1), (1, 5)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 0), (1, 5)) := by decide
example : ¬ BoundedCut (edge, [[0, 5]], (0, 1), (1, 5)) := by decide
example : ¬ BoundedCut (edge, [[0, 5], [4, 0]], (0, 1), (1, 5)) := by decide
example : BoundedCut (edge, costs, (0, 1), (1, 5)) := by decide
example : BoundedCut (edge, costs, (1, 0), (1, 5)) := by decide
example : ¬ BoundedCut (edge, costs, (0, 1), (1, 4)) := by decide
example : ¬ BoundedCut (edge, [[0, 0], [0, 0]], (0, 1), (1, 1)) := by decide
example : BoundedCut (isolated, [[0, 0], [0, 0]], (0, 1), (1, 1)) := by decide
example : BoundedCut (isolated, costs, (0, 1), (1, 1)) := by decide
example : BoundedCut (edge, costs, (0, 1), (2, 5)) := by decide
example : ¬ BoundedCut (chain, [[0, 1, 0], [1, 0, 1], [0, 1, 0]], (0, 2), (1, 9)) :=
  by decide
example : BoundedCut (chain, [[0, 1, 0], [1, 0, 1], [0, 1, 0]], (0, 2), (2, 1)) :=
  by decide

example : bitDecode (bitEncode ((edge, [1, 2], costs, 3, 1) : WeightedPartitionInput)) =
    some ((edge, [1, 2], costs, 3, 1) : WeightedPartitionInput) := bitDecode_bitEncode _
example : bitDecode (bitEncode ((edge, costs, (0, 1), (1, 5)) : BoundedCutInput)) =
    some ((edge, costs, (0, 1), (1, 5)) : BoundedCutInput) := bitDecode_bitEncode _
example : bitDecode (bitEncode ((square, 2) : Code × ℕ)) = some ((square, 2) : Code × ℕ) :=
  bitDecode_bitEncode _

theorem nonvacuous_machine_interface :
    ComplexityTheory.HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (CliquePartition (edge, 1)), decide (TrianglePartition chain),
  decide (BalancedBiclique (square, 2)))

/-- info: (false, true, false) -/
#guard_msgs in
#eval (decide (WeightedPartition (edge, [1, 1], costs, 1, 4)),
  decide (WeightedPartition (edge, [1, 1], costs, 1, 5)),
  decide (BoundedCut (edge, costs, (0, 0), (1, 5))))

end Computability.GraphPartitionProblems.Test
