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

public meta import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Boundary and witness tests for matrix-encoded graph decision problems -/

@[expose] public section

namespace Computability.MatrixGraph.Test

open BitstringEncoding ComplexityTheory

def isolated : Code := [[false]]
def edge : Code := [[false, true], [true, false]]
def triangle : Code :=
  [[false, true, true], [true, false, true], [true, true, false]]
def directedTriangle : Code :=
  [[false, true, false], [false, false, true], [true, false, false]]
def directedPath : Code :=
  [[false, true, false], [false, false, true], [false, false, false]]
def disjointEdges : Code :=
  [[false, true, false, false], [true, false, false, false],
    [false, false, false, true], [false, false, true, false]]

example : ValidGraph [] := by decide
example : ValidGraph isolated := by decide
example : ValidGraph edge := by decide
example : ValidGraph triangle := by decide
example : ValidDigraph directedTriangle := by decide
example : ¬ ValidGraph directedTriangle := by decide
example : ¬ ValidGraph [[true]] := by decide
example : ¬ ValidDigraph [[true]] := by decide
example : ¬ ValidGraph [[false, true]] := by decide
example : ¬ ValidGraph [[false], [false, false]] := by decide

example : Clique (isolated, 1) := by decide
example : ¬ Clique (isolated, 2) := by decide
example : Clique (triangle, 3) := by decide
example : Clique (triangle, 2) := by decide
example : ¬ Clique (triangle, 4) := by decide
example : ¬ Clique (triangle, 0) := by decide
example : ¬ Clique (directedTriangle, 2) := by decide

example : VertexCover (isolated, 1) := by decide
example : VertexCover (edge, 1) := by decide
example : VertexCover (edge, 3) := by decide
example : ¬ VertexCover (triangle, 1) := by decide
example : VertexCover (triangle, 2) := by decide
example : ¬ VertexCover (edge, 0) := by decide

example : Colorable (isolated, 1) := by decide
example : ¬ Colorable (edge, 1) := by decide
example : Colorable (edge, 2) := by decide
example : ¬ Colorable (triangle, 2) := by decide
example : Colorable (triangle, 3) := by decide
example : Colorable ([], 1) := by decide
example : ¬ Colorable ([], 0) := by decide

example : DirectedHamiltonian directedTriangle := by decide
example : ¬ DirectedHamiltonian directedPath := by decide
example : DirectedHamiltonian edge := by decide
example : ¬ UndirectedHamiltonian edge := by decide
example : UndirectedHamiltonian triangle := by decide
example : ¬ UndirectedHamiltonian directedTriangle := by decide
example : ¬ DirectedHamiltonian [] := by decide
example : ¬ DirectedHamiltonian isolated := by decide
example : ¬ UndirectedHamiltonian isolated := by decide
example : ¬ DirectedHamiltonian disjointEdges := by decide
example : ¬ UndirectedHamiltonian disjointEdges := by decide

example (a : Code) : bitDecode (bitEncode a) = some a := by simp
example : (bitEncode triangle).length = 57 := by decide
example : (bitEncode edge).length = 26 := by decide

theorem nonvacuous_machine_interface : HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (Clique (triangle, 3)), decide (Colorable (triangle, 2)),
  decide (VertexCover (triangle, 2)))

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (DirectedHamiltonian edge), decide (UndirectedHamiltonian edge),
  decide (UndirectedHamiltonian triangle))

end Computability.MatrixGraph.Test
