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

public meta import FormalConjecturesForMathlib.Computability.FiniteSetProblems
public import FormalConjecturesForMathlib.Computability.FiniteSetProblems
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Boundary and witness tests for finite-set decision problems -/

@[expose] public section

namespace Computability.FiniteSetProblems.Test

open BitstringEncoding ComplexityTheory

example : row [[7, 7, 9]] 0 = {7, 9} := by decide
example : ground [] = ∅ := by decide
example : ground [[1000000], [3, 1000000], []] = {3, 1000000} := by decide
example : DisjointRows [[], []] Finset.univ := by decide
example : ¬ DisjointRows [[1], [1]] Finset.univ := by decide

example : ¬ SetPacking ([], 1) := by decide
example : ¬ SetPacking ([[1]], 0) := by decide
example : SetPacking ([[1]], 1) := by decide
example : ¬ SetPacking ([[1]], 2) := by decide
example : SetPacking ([[1, 2], [3, 4]], 2) := by decide
example : ¬ SetPacking ([[1, 2], [2, 3]], 2) := by decide
example : SetPacking ([[1, 2], [2, 3], [4]], 2) := by decide
example : ¬ SetPacking ([[1, 2], [2, 3], [4]], 3) := by decide
example : SetPacking ([[], []], 2) := by decide
example : ¬ SetPacking ([[1], [1]], 2) := by decide
example : SetPacking ([[1, 1], [2, 2]], 2) := by decide

example : SetCovering ([], 1) := by decide
example : ¬ SetCovering ([], 0) := by decide
example : SetCovering ([[1, 2], [2, 3]], 2) := by decide
example : ¬ SetCovering ([[1, 2], [2, 3]], 1) := by decide
example : SetCovering ([[1, 2], [2, 3], [1, 2, 3]], 1) := by decide
example : SetCovering ([[1], [2]], 5) := by decide
example : SetCovering ([[1, 1], [1]], 1) := by decide
example : SetCovering ([[], []], 1) := by decide

example : ValidFamily [1, 2] [[1], [2, 2], []] := by decide
example : ¬ ValidFamily [1] [[1, 2]] := by decide
example : ExactCover ([], []) := by decide
example : ExactCover ([], [[]]) := by decide
example : ¬ ExactCover ([1], []) := by decide
example : ExactCover ([1, 2, 3], [[1, 2], [3]]) := by decide
example : ¬ ExactCover ([1, 2, 3], [[1, 2], [2, 3]]) := by decide
example : ¬ ExactCover ([1, 2, 3], [[1], [2]]) := by decide
example : ¬ ExactCover ([1], [[1], [2]]) := by decide
example : ExactCover ([1, 1, 2], [[1, 1], [2]]) := by decide
example : ExactCover ([1], [[1], [1]]) := by decide

example : ExactHitting [] := by decide
example : ¬ ExactHitting [[]] := by decide
example : ExactHitting [[1, 2], [2, 3]] := by decide
example : ¬ ExactHitting [[1], [2], [1, 2]] := by decide
example : ¬ ExactHitting [[1, 2], [2, 3], [1, 3]] := by decide
example : ExactHitting [[1, 2], [2, 3], [3, 4], [4, 1]] := by decide
example : ExactHitting [[1000000, 1000000], [1000000]] := by decide
example : ¬ ExactHitting [[1], []] := by decide

example : ThreeDimensionalMatching ([], []) := by decide
example : ¬ ThreeDimensionalMatching ([0], []) := by decide
example : ThreeDimensionalMatching ([0], [(0, 0, 0)]) := by decide
example : ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (1, 1, 1)]) := by decide
example : ThreeDimensionalMatching ([0, 1], [(0, 1, 0), (1, 0, 1)]) := by decide
example : ¬ ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (0, 1, 1)]) := by decide
example : ¬ ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (1, 0, 1)]) := by decide
example : ¬ ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (1, 1, 0)]) := by decide
example : ¬ ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (0, 0, 0)]) := by decide
example : ThreeDimensionalMatching ([0, 0], [(0, 0, 0), (0, 0, 0)]) := by decide
example : ¬ ValidMatching ([0], [(0, 0, 1)]) := by decide
example : ¬ ThreeDimensionalMatching ([0], [(0, 0, 0), (0, 0, 1)]) := by decide
example : ¬ ThreeDimensionalMatching ([], [(0, 0, 0)]) := by decide
example : ThreeDimensionalMatching ([17, 1000000],
    [(17, 1000000, 17), (1000000, 17, 1000000)]) := by decide

example (input : Family × ℕ) : bitDecode (bitEncode input) = some input := by simp
example (input : List ℕ × Family) : bitDecode (bitEncode input) = some input := by simp
example (input : Family) : bitDecode (bitEncode input) = some input := by simp
example (input : MatchingInput) : bitDecode (bitEncode input) = some input := by simp

/-- The shared interface admits an actual polynomial-time function, independently of these
five open lower-bound statements. -/
theorem nonvacuous_machine_interface : HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (SetPacking ([[1], [2]], 2)),
  decide (ExactHitting [[1], [2], [1, 2]]),
  decide (ExactCover ([1, 2], [[1], [2]])))

/-- info: (false, true, false) -/
#guard_msgs in
#eval (decide (SetCovering ([[1], [2]], 1)),
  decide (ThreeDimensionalMatching ([0], [(0, 0, 0)])),
  decide (ThreeDimensionalMatching ([0, 1], [(0, 0, 0), (1, 1, 0)])))

end Computability.FiniteSetProblems.Test
