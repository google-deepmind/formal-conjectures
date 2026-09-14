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

public meta import FormalConjecturesForMathlib.Computability.BooleanSatisfiability
public import FormalConjecturesForMathlib.Computability.BooleanSatisfiability
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Arity, polarity, occurrence, and shared-assignment tests for Boolean satisfiability -/

@[expose] public section

namespace Computability.BooleanSatisfiability.Test

open BitstringEncoding ComplexityTheory

example : evalLiteral ∅ (0, true) = false := by decide
example : evalLiteral ∅ (0, false) = true := by decide
example : evalLiteral {0} (0, true) = true := by decide
example : evalLiteral {0} (0, false) = false := by decide
example : evalLiteral {9} (0, true) = false := by decide
example : support [] = ∅ := by decide
example : support [[]] = ∅ := by decide
example : support [[(0, true), (0, false)], [(1000000, true)]] = {0, 1000000} := by decide
example : (support [[(1000000, true)]]).card = 1 := by decide
example : SatisfiableWith (fun _ ↦ false) [] := by decide
example : ¬ SatisfiableWith (fun _ ↦ false) [[]] := by decide
example : SatisfiableWith (fun _ ↦ true) [[]] := by decide
example : ExactlyThree [] := by decide
example : ¬ ExactlyThree [[]] := by decide
example : ExactlyThree [[(0, true), (0, true), (0, true)]] := by decide

example : ThreeSat [] := by decide
example : ¬ ThreeSat [[]] := by decide
example : ThreeSat [[(0, true)]] := by decide
example : ThreeSat [[(0, false)]] := by decide
example : ¬ ThreeSat [[(0, true)], [(0, false)]] := by decide
example : ThreeSat [[(0, true), (0, false)]] := by decide
example : ThreeSat [[(0, true), (0, true), (0, true)]] := by decide
example : ¬ ThreeSat [[(0, true), (0, true), (0, true), (0, false)]] := by decide
example : ThreeSat [[(1000000, true)], [(2, false)]] := by decide
example : ¬ ThreeSat [[(1000000, true)], [(1000000, false)]] := by decide
example : ThreeSat [[(0, true), (1, true)], [(0, false), (1, false)]] := by decide
example : ¬ ThreeSat
    [[(0, true), (1, true)], [(0, false)], [(1, false)]] := by decide

example : OneInThree [] := by decide
example : ¬ OneInThree [[]] := by decide
example : ¬ OneInThree [[(0, true)]] := by decide
example : ¬ OneInThree [[(0, true), (1, true)]] := by decide
example : ¬ OneInThree [[(0, true), (1, true), (2, true), (3, true)]] := by decide
example : ¬ OneInThree [[(0, true), (0, true), (0, true)]] := by decide
example : OneInThree [[(0, true), (0, true), (1, true)]] := by decide
example : OneInThree [[(0, true), (0, false), (0, false)]] := by decide
example : OneInThree [[(0, false), (0, true), (0, true)]] := by decide
-- The first clause forces variable 0 true; the second forces it false.
example : ¬ OneInThree
    [[(0, true), (0, false), (0, false)], [(0, false), (0, true), (0, true)]] := by decide
example : OneInThree [[(0, false), (1, false), (2, false)]] := by decide

example : NotAllEqual [] := by decide
example : ¬ NotAllEqual [[]] := by decide
example : ¬ NotAllEqual [[(0, true)]] := by decide
example : ¬ NotAllEqual [[(0, true), (0, false)]] := by decide
example : ¬ NotAllEqual [[(0, true), (1, true), (2, true), (3, true)]] := by decide
example : ¬ NotAllEqual [[(0, true), (0, true), (0, true)]] := by decide
example : NotAllEqual [[(0, true), (0, true), (0, false)]] := by decide
example : NotAllEqual [[(0, false), (0, false), (0, true)]] := by decide
example : NotAllEqual [[(0, true), (0, true), (1, true)]] := by decide
example : NotAllEqual [[(0, true), (0, true), (1, false)]] := by decide
-- The first clause forces unequal values; the second forces equal values.
example : ¬ NotAllEqual
    [[(0, true), (0, true), (1, true)], [(0, true), (0, true), (1, false)]] := by decide

/-- Schaefer's repeated-argument example on p. 216, with x=0, y=1, z=2, u=3. -/
def schaeferExample : PositiveFormula := [[0, 1, 2], [0, 1, 3], [3, 3, 1]]

example : positiveEmbedding [[0, 0, 1]] = [[(0, true), (0, true), (1, true)]] := by decide
example : PositiveOneInThree [] := by decide
example : ¬ PositiveOneInThree [[]] := by decide
example : ¬ PositiveOneInThree [[0]] := by decide
example : ¬ PositiveOneInThree [[0, 1]] := by decide
example : ¬ PositiveOneInThree [[0, 1, 2, 3]] := by decide
example : PositiveOneInThree schaeferExample := by decide
example : ∀ clause ∈ positiveEmbedding schaeferExample,
    (clause.map (evalLiteral {1})).count true = 1 := by decide
example : ¬ PositiveOneInThree [[0, 0, 0]] := by decide
example : PositiveOneInThree [[0, 0, 1]] := by decide
example : PositiveOneInThree [[1, 0, 0]] := by decide
example : ¬ PositiveOneInThree [[0, 0, 1], [1, 1, 0]] := by decide
example : PositiveOneInThree [[1000000, 1000000, 2]] := by decide
example : PositiveOneInThree [[0, 1, 2], [0, 1, 2]] := by decide

example : PositiveNotAllEqual [] := by decide
example : ¬ PositiveNotAllEqual [[]] := by decide
example : ¬ PositiveNotAllEqual [[0]] := by decide
example : ¬ PositiveNotAllEqual [[0, 1]] := by decide
example : ¬ PositiveNotAllEqual [[0, 1, 2, 3]] := by decide
example : ¬ PositiveNotAllEqual [[0, 0, 0]] := by decide
example : PositiveNotAllEqual [[0, 0, 1]] := by decide
example : PositiveNotAllEqual [[1, 0, 0]] := by decide
example : PositiveNotAllEqual schaeferExample := by decide
example : PositiveNotAllEqual [[1000000, 1000000, 2]] := by decide
example : PositiveNotAllEqual [[0, 0, 1], [1, 1, 0]] := by decide
example : ¬ PositiveNotAllEqual [[0, 0, 1], [1, 1, 2], [2, 2, 0]] := by decide
example : PositiveNotAllEqual [[0, 0, 1], [1, 1, 2], [2, 2, 3], [3, 3, 0]] := by decide

/-- All four triples on four variables distinguish exactly-one from not-all-equal. -/
def fourTriples : PositiveFormula := [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

example : ¬ PositiveOneInThree fourTriples := by decide
example : PositiveNotAllEqual fourTriples := by decide
example : ThreeSat (positiveEmbedding fourTriples) := by decide

example (input : Formula) : bitDecode (bitEncode input) = some input := by simp
example (input : PositiveFormula) : bitDecode (bitEncode input) = some input := by simp
set_option maxRecDepth 2048 in
example : (bitEncode ([[(1000000, true)]] : Formula)).length < 256 := by decide
set_option maxRecDepth 2048 in
example : (bitEncode ([[1000000]] : PositiveFormula)).length < 256 := by decide

/-- An existing polynomial-time machine witnesses that the decider interface is nonvacuous. -/
theorem nonvacuous_machine_interface : HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (PositiveOneInThree schaeferExample),
  decide (PositiveOneInThree fourTriples), decide (PositiveNotAllEqual fourTriples))

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (ThreeSat [[(1000000, true)]]),
  decide (PositiveNotAllEqual [[0, 0, 1], [1, 1, 2], [2, 2, 0]]),
  decide (NotAllEqual [[(0, true), (0, true), (0, false)]]))

end Computability.BooleanSatisfiability.Test
