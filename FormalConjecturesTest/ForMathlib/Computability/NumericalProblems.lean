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

public meta import FormalConjecturesForMathlib.Computability.NumericalProblems
public import FormalConjecturesForMathlib.Computability.NumericalProblems
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Boundary, multiplicity, and weight tests for numerical decision problems -/

@[expose] public section

namespace Computability.NumericalProblems.Test

open BitstringEncoding ComplexityTheory

example : SubsetSum ([], 0) := by decide
example : ¬ SubsetSum ([], 1) := by decide
example : SubsetSum ([3, 3], 6) := by decide
example : ¬ SubsetSum ([3], 6) := by decide
example : SubsetSum ([3, -5], -2) := by decide
example : SubsetSum ([3, -5], -5) := by decide
example : ¬ SubsetSum ([3, -5], 2) := by decide
example : SubsetSum ([0, 0], 0) := by decide
example : SubsetSum ([2, 4, 8], 6) := by decide
example : ¬ SubsetSum ([2, 4, 8], 7) := by decide
example : SubsetSum ([1000000, 1000000], 2000000) := by decide

example : Partition [] := by decide
example : Partition [0] := by decide
example : ¬ Partition [1] := by decide
example : Partition [3, 3] := by decide
example : ¬ Partition [3, 3, 3] := by decide
example : Partition [1, 2, 3] := by decide
example : ¬ Partition [1, 2, 4] := by decide
example : Partition [-2, -2] := by decide
example : Partition [-5, 5] := by decide
example : ¬ Partition [-5, 3] := by decide
example : Partition [1000000, 1000000] := by decide

example : ValidIntegerProgram ([], [0]) := by decide
example : ValidIntegerProgram ([[], []], []) := by decide
example : ¬ ValidIntegerProgram ([[1]], [0, 0]) := by decide
example : ¬ ValidIntegerProgram ([[1, 2], [3]], [0, 0]) := by decide
example : ZeroOneProgramming ([], []) := by decide
example : ZeroOneProgramming ([], [0, 0]) := by decide
example : ¬ ZeroOneProgramming ([], [0, 1]) := by decide
example : ZeroOneProgramming ([[], []], []) := by decide
example : ZeroOneProgramming ([[1, 0], [0, 1]], [1, 1]) := by decide
example : ¬ ZeroOneProgramming ([[1, 1]], [1, 0]) := by decide
example : ZeroOneProgramming ([[3], [3]], [6]) := by decide
example : ¬ ZeroOneProgramming ([[3]], [6]) := by decide
example : ZeroOneProgramming ([[3], [-5]], [-2]) := by decide
example : ¬ ZeroOneProgramming ([[2]], [1]) := by decide
example : ¬ ZeroOneProgramming ([[0]], [0, 0]) := by decide
example : ¬ ZeroOneProgramming ([[0, 0]], [0]) := by decide
example : ZeroOneProgramming ([[1, 0, 2], [0, 1, 3]], [1, 1, 5]) := by decide
example : ¬ ZeroOneProgramming ([[1, 0, 2], [0, 1, 3]], [1, 1, 4]) := by decide

def schedule : List Job := [(3, 4, 7), (1, 1, 5)]

example : ValidJobs [] := by decide
example : ValidJobs schedule := by decide
example : ¬ ValidJobs [(0, 1, 1)] := by decide
example : ¬ ValidJobs [(1, 0, 1)] := by decide
example : ¬ ValidJobs [(1, 1, 0)] := by decide
example : completionTime schedule (Equiv.refl _) ⟨0, by decide⟩ = 3 := by decide
example : completionTime schedule (Equiv.refl _) ⟨1, by decide⟩ = 4 := by decide
example : latePenalty schedule (Equiv.refl _) = 5 := by decide
example : latePenalty schedule (Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩) = 0 := by decide
example : latePenalty [(2, 1, 5)] (Equiv.refl _) = 5 := by decide
example : JobSequencing (schedule, 1) := by decide
example : JobSequencing ([], 1) := by decide
example : ¬ JobSequencing ([], 0) := by decide
example : JobSequencing ([(1, 1, 9)], 1) := by decide
example : ¬ JobSequencing ([(2, 1, 5)], 4) := by decide
example : JobSequencing ([(2, 1, 5)], 5) := by decide
example : ¬ JobSequencing ([(1, 1, 5), (1, 1, 5)], 4) := by decide
example : JobSequencing ([(1, 1, 5), (1, 1, 5)], 5) := by decide
example : ¬ JobSequencing ([(0, 1, 1)], 10) := by decide
example : ¬ JobSequencing ([(1, 0, 1)], 10) := by decide
example : ¬ JobSequencing ([(1, 1, 0)], 10) := by decide

def edge : WeightMatrix := [[0, 3], [3, 0]]
def triangle : WeightMatrix := [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
def signedTriangle : WeightMatrix := [[0, 5, -10], [5, 0, 5], [-10, 5, 0]]

example : ValidWeightMatrix [] := by decide
example : ValidWeightMatrix [[0]] := by decide
example : ValidWeightMatrix edge := by decide
example : ValidWeightMatrix signedTriangle := by decide
example : ¬ ValidWeightMatrix [[1]] := by decide
example : ¬ ValidWeightMatrix [[0, 1], [2, 0]] := by decide
example : ¬ ValidWeightMatrix [[0, 3], [3]] := by decide
example : cutWeight edge {⟨0, by decide⟩} = 3 := by decide
example : cutWeight edge {⟨1, by decide⟩} = 3 := by decide
example : cutWeight edge ∅ = 0 := by decide
example : cutWeight edge Finset.univ = 0 := by decide
example : WeightedMaxCut (edge, 3) := by decide
example : ¬ WeightedMaxCut (edge, 4) := by decide
example : ¬ WeightedMaxCut (edge, 6) := by decide
example : ¬ WeightedMaxCut (edge, 0) := by decide
example : ¬ WeightedMaxCut ([], 1) := by decide
example : ¬ WeightedMaxCut ([[0]], 1) := by decide
example : WeightedMaxCut (triangle, 2) := by decide
example : ¬ WeightedMaxCut (triangle, 3) := by decide
example : WeightedMaxCut (signedTriangle, 10) := by decide
example : ¬ WeightedMaxCut (signedTriangle, 11) := by decide
example : ¬ WeightedMaxCut ([[0, -3], [-3, 0]], 1) := by decide
example : ¬ WeightedMaxCut ([[0, 5], [0, 0]], 1) := by decide
example : ¬ WeightedMaxCut ([[0, 5], [5]], 1) := by decide

example (input : List ℤ × ℤ) : bitDecode (bitEncode input) = some input := by simp
example (input : List ℤ) : bitDecode (bitEncode input) = some input := by simp
example (input : IntegerProgramInput) : bitDecode (bitEncode input) = some input := by simp
example (input : List Job × ℕ) : bitDecode (bitEncode input) = some input := by simp
example (input : WeightMatrix × ℕ) : bitDecode (bitEncode input) = some input := by simp
set_option maxRecDepth 2048 in
example : (bitEncode ([1000000, 1000000] : List ℤ)).length < 300 := by decide
set_option maxRecDepth 2048 in
example : (bitEncode (([[1000000]], [1000000]) : IntegerProgramInput)).length < 512 := by
  decide

/-- An existing polynomial-time machine witnesses that the decider interface is nonvacuous. -/
theorem nonvacuous_machine_interface : HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (SubsetSum ([3, 3], 6)),
  decide (ZeroOneProgramming ([[2]], [1])),
  decide (Partition [3, 3]))

/-- info: (true, true, false) -/
#guard_msgs in
#eval (decide (JobSequencing (schedule, 1)),
  decide (WeightedMaxCut (signedTriangle, 10)),
  decide (WeightedMaxCut (edge, 4)))

end Computability.NumericalProblems.Test
