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

public import FormalConjecturesForMathlib.Computability.FineGrainedProblems
public meta import FormalConjecturesForMathlib.Computability.FineGrainedProblems
public meta import FormalConjecturesForMathlib.Computability.WordRAM

/-!
# Word-RAM and fine-grained input tests

Kernel-checked tests only; no research statements are imported.
-/

@[expose] public section

namespace FineGrainedTest

open WordRAM FineGrained Computability.BooleanSatisfiability

example : word 4 19 = 3 := rfl
example : word 0 19 = 0 := rfl
example : BinaryOp.eval .add 4 15 2 = 1 := rfl
example : BinaryOp.eval .sub 4 0 1 = 15 := rfl
example : BinaryOp.eval .mul 4 7 3 = 5 := rfl
example : BinaryOp.eval .div 4 15 4 = 3 := rfl
example : BinaryOp.eval .div 4 15 0 = 0 := rfl
example : BinaryOp.eval .mod 4 15 4 = 3 := rfl
example : BinaryOp.eval .mod 4 15 0 = 15 := rfl
example : BinaryOp.eval .bitAnd 4 10 6 = 2 := rfl
example : BinaryOp.eval .bitOr 4 10 6 = 14 := rfl
example : BinaryOp.eval .bitXor 4 10 6 = 12 := rfl
example : BinaryOp.eval .shiftLeft 4 3 2 = 12 := rfl
example : BinaryOp.eval .shiftLeft 4 3 4 = 0 := rfl
example : BinaryOp.eval .shiftRight 4 12 2 = 3 := rfl
example : BinaryOp.eval .shiftRight 4 12 4 = 0 := rfl
example : Comparison.eval .equal 2 2 = true := rfl
example : Comparison.eval .less 2 3 = true := rfl
example : Comparison.eval .less 3 2 = false := rfl

example : logarithmicWidth 1 0 = 2 := rfl
example : logarithmicWidth 1 6 = 4 := rfl
example : logarithmicWidth 3 6 = 12 := rfl
example (n : ℕ) : n < 2 ^ logarithmicWidth 1 n := input_fits n

example : execute [] 4 [] [] 0 = none := rfl
example : execute [] 4 [] [] 1 = some false := rfl
example : execute [.halt 0] 4 [] [] 1 = some false := rfl
example : execute [.literal 0 1, .halt 0] 4 [] [] 1 = none := rfl
example : execute [.literal 0 1, .halt 0] 4 [] [] 2 = some true := rfl

/-- The address comes from a register, with modular address semantics. -/
def memoryProgram : Program :=
  [.literal 0 19, .literal 1 1, .store 0 1, .literal 0 3, .load 2 0, .halt 2]

example : execute memoryProgram 4 [] [] 6 = some true := rfl
example : execute memoryProgram 5 [] [] 6 = some false := rfl

/-- Jumping over a false answer reaches the true answer. -/
def branchProgram : Program :=
  [.literal 0 2, .literal 1 3, .branch .less 0 1 5 3, .literal 2 0,
    .halt 2, .literal 2 1, .halt 2]

example : execute branchProgram 4 [] [] 5 = some true := rfl
example : execute [.jump 0] 4 [] [] 10 = none := rfl
example : execute [.jump 20] 4 [] [] 2 = some false := rfl
example : execute [.inputLength 0, .halt 0] 4 [false] [] 2 = some true := rfl
example : execute [.wordWidth 0, .halt 0] 4 [] [] 2 = some true := rfl
example : execute [.literal 0 1, .readInput 1 0, .halt 1] 4 [true, false] [] 3 =
    some false := rfl
example : execute [.literal 0 1, .readInput 1 0, .halt 1] 4 [false, true] [] 3 =
    some true := rfl
example : execute [.literal 0 8, .readInput 1 0, .halt 1] 4 [true] [] 3 =
    some false := rfl

/-- Two coin instructions consume different random bits. -/
def secondCoin : Program := [.coin 0, .coin 0, .halt 0]

example : execute secondCoin 4 [] [false, true] 3 = some true := rfl
example : execute secondCoin 4 [] [true, false] 3 = some false := rfl
example (extra : List Bool) :
    execute secondCoin 4 [] ([false, true, false] ++ extra) 3 = some true := by
  rw [execute_append_coins secondCoin 4 [] [false, true, false] extra 3 (by decide)]
  rfl
example : correctCount [.coin 0, .halt 0] 4 [] 2 true = 2 := by decide
example : correctCount [.coin 0, .halt 0] 4 [] 2 false = 2 := by decide
example : ¬ BoundedError [.coin 0, .halt 0] 4 [] 2 true := by decide
example : ¬ BoundedError [.coin 0, .halt 0] 4 [] 2 false := by decide

/-- Success on three of the four first-coin pairs is above the two-thirds threshold. -/
def twoCoinOr : Program := [.coin 0, .coin 1, .binary 2 .bitOr 0 1, .halt 2]

example : correctCount twoCoinOr 4 [] 4 true = 12 := by decide
example : BoundedError twoCoinOr 4 [] 4 true := by decide
example : ¬ BoundedError twoCoinOr 4 [] 4 false := by decide

theorem false_program_certain (input : List Bool) :
    BoundedError [.halt 0] 4 input 1 false :=
  boundedError_of_certain (fun _ => rfl)

theorem true_program_certain (input : List Bool) :
    BoundedError [.literal 0 1, .halt 0] 4 input 2 true :=
  boundedError_of_certain (fun _ => rfl)

/-- The complexity predicate admits an actual uniform constant-output program. -/
theorem constant_false_fast :
    HasFastDecider (fun _ : Bool => True) (fun _ => false) (fun _ => 1) := by
  refine ⟨[.halt 0], 1, 1, by decide, by decide, ?_⟩
  intro x _
  apply boundedError_of_certain
  intro v
  simp [execute, run, step, word]

/-- The rational-power interface also admits constant time at exponent zero. -/
theorem constant_false_power :
    HasPowerTimeDecider (fun _ : Bool => True) (fun _ => false)
      (fun _ => 0) (fun _ => 1) 0 1 := by
  refine ⟨by decide, [.halt 0], 1, 1, by decide, by decide, ?_⟩
  intro x _
  refine ⟨1, by simp, ?_⟩
  apply boundedError_of_certain
  intro v
  simp [execute, run, step, word]

example : ¬ BoundedError [.jump 0] 4 [] 3 false := by decide
example : ¬ BoundedError [] 4 [] 0 false := not_boundedError_zero [] 4 [] false

example : WidthAtMost 3 [] := by decide
example : WidthAtMost 3 [[]] := by decide
example : sat [] = true := by decide
example : sat [[]] = false := by decide
example : sat [[(0, true)], [(0, false)]] = false := by decide
example : sat [[(0, true), (0, false)]] = true := by decide
example : ¬ WidthAtMost 3 [[(0, true), (1, true), (2, true), (3, true)]] := by decide
example : variableCount [[(1000000, true), (1000000, false)]] = 1 := by decide
example : variableCount [[(7, true)], [(42, true)]] = 2 := by decide
example : satTime 1 2 0 [[(7, true)], [(42, true)]] = 2 := by decide
example : satTime 1 3 0 [[(7, true)], [(42, true)]] = 1 := by decide
example : satTime 0 3 0 [[(7, true)], [(42, true)]] = 1 := by decide
example : ¬ HasSatTime 3 1 0 := by simp [HasSatTime]

example : ValidOV (0, ([[]], [[]])) := by decide
example : orthogonalVectors (0, ([[]], [[]])) = true := by decide
example : orthogonalVectors (0, ([], [])) = false := by decide
example : ValidOV (2, ([[true, false]], [[false, true]])) := by decide
example : orthogonalVectors (2, ([[true, false]], [[false, true]])) = true := by decide
example : orthogonalVectors (2, ([[true, false]], [[true, false]])) = false := by decide
example : ¬ ValidOV (2, ([[true]], [[false, true]])) := by decide
example : ¬ ValidOV (1, ([[true], [true]], [[true], [false]])) := by decide
example : ¬ ValidOV (1, ([[true]], [])) := by decide
example : ¬ Orthogonal [true] [] := by decide
example : Orthogonal [false] [false] := by decide
example : Orthogonal [false] [true] := by decide
example : Orthogonal [true] [false] := by decide
example : ¬ Orthogonal [true] [true] := by decide
example : Orthogonal [false, false] [true, true] := by decide
example : ¬ Orthogonal [true, false] [true, false] := by decide
example : ¬ Orthogonal [true, true] [true, true] := by decide

example : ValidThreeSum [-1, 0, 1] := by decide
example : ThreeSum [-1, 0, 1] := by decide
example : ¬ ThreeSum [0] := by decide
example : ¬ ThreeSum [0, 0] := by decide
example : ¬ ValidThreeSum [0, 0, 0] := by decide
example : ¬ ThreeSum [1, 2, 3] := by decide
example : ValidThreeSum [-81, 0, 81] := by decide
example : ¬ ValidThreeSum [-82, 0, 82] := by decide

/-- An undirected triangle whose edge weights sum to zero. -/
def zeroTriangle : WeightedGraph :=
  [[(false, 0), (true, -2), (true, 1)],
   [(true, -2), (false, 0), (true, 1)],
   [(true, 1), (true, 1), (false, 0)]]

example : ValidWeightedGraph 1 zeroTriangle := by decide
example : ExactTriangle zeroTriangle := by decide
example : ¬ ExactTriangle [] := by decide
example : ¬ ExactTriangle [[(false, 0)]] := by decide
example : ¬ ExactTriangle [[(true, 0)]] := by decide
example : ¬ ValidWeightedGraph 300 [[(true, 0)]] := by decide
example : ¬ ValidWeightedGraph 300 [[(false, 0), (false, 0)]] := by decide
example : ¬ ValidWeightedGraph 1 [[(false, 2)]] := by decide
example : ¬ ExactTriangle
    [[(false, 0), (true, -2), (false, 1)],
     [(true, -2), (false, 0), (true, 1)],
     [(false, 1), (true, 1), (false, 0)]] := by decide
example : ¬ ExactTriangle
    [[(false, 0), (true, -3), (true, 1)],
     [(true, -3), (false, 0), (true, 1)],
     [(true, 1), (true, 1), (false, 0)]] := by decide

example : ¬ HasPowerTimeDecider ValidThreeSum threeSum List.length (fun _ => 1) 1 0 :=
  not_hasPowerTimeDecider_zero ValidThreeSum threeSum List.length (fun _ => 1) 1

#guard execute memoryProgram 4 [] [] 6 == some true
#guard execute secondCoin 4 [] [true, false] 3 == some false
#guard exactTriangle zeroTriangle
#guard !sat [[]]

end FineGrainedTest
