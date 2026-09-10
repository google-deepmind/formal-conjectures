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
import FormalConjecturesForMathlib.Computability.ExactCounting
import FormalConjecturesForMathlib.Computability.TotalSearch
import FormalConjecturesForMathlib.Computability.HypergraphEnumeration

/-!
# Boundary tests for exact counting, total search and enumeration
-/

namespace SearchCountingTest

open EncodedBooleanCircuit TotalSearch ExactCounting HypergraphEnumeration

example : modelCount [] = 1 := by decide +kernel
example : modelCount [[]] = 0 := by decide +kernel
example : modelCount [[(0, true)]] = 1 := by decide +kernel
example : modelCount [[(0, true), (0, false)]] = 2 := by decide +kernel
example : modelCount [[(0, true)], [(0, false)]] = 0 := by decide +kernel
example : modelCount [[(0, true), (1, true)]] = 3 := by decide +kernel
example : modelCount [[(1000000, true), (1000000, false)]] = 2 := by decide +kernel
example : modelCount [[(0, true), (0, true)]] = 1 := by decide +kernel
example : modelCount [[(0, true)], [(0, true)]] = 1 := by decide +kernel

example : ExactCounting.permanent [] = 1 := by decide +kernel
example : ExactCounting.permanent [[false]] = 0 := by decide +kernel
example : ExactCounting.permanent [[true]] = 1 := by decide +kernel
example : ExactCounting.permanent [[true, false], [false, true]] = 1 := by decide +kernel
example : ExactCounting.permanent [[true, true], [true, true]] = 2 := by decide +kernel
example : ExactCounting.permanent [[false, true], [true, false]] = 1 := by decide +kernel
example : ExactCounting.permanent [[true, true], [false, false]] = 0 := by decide +kernel
example : ExactCounting.permanent [[true, true]] = 0 := by decide +kernel
example : ExactCounting.permanent [[], []] = 0 := by decide +kernel

def id1 : Circuit := (⟨1⟩, [], [(false, 0)])
def not1 : Circuit := (⟨1⟩, [.not (false, 0)], [(true, 0)])
def zero1 : Circuit :=
  (⟨1⟩, [.not (false, 0), .and (false, 0) (true, 0)], [(true, 1)])
def one1 : Circuit :=
  (⟨1⟩, [.not (false, 0), .or (false, 0) (true, 0)], [(true, 1)])
def source2 : Circuit :=
  (⟨2⟩, [.not (false, 0), .or (false, 0) (true, 0)], [(true, 1), (false, 1)])
def pred2 : Circuit :=
  (⟨2⟩, [.not (false, 0), .and (false, 0) (true, 0)], [(true, 1), (false, 1)])

example : Valid id1 := by decide +kernel
example : Valid not1 := by decide +kernel
example : Valid zero1 := by decide +kernel
example : Valid one1 := by decide +kernel
example : eval id1 [true] = [true] := by decide +kernel
example : eval not1 [true] = [false] := by decide +kernel
example : eval zero1 [true] = [false] := by decide +kernel
example : eval one1 [false] = [true] := by decide +kernel
example : ¬ Valid (⟨1⟩, [.not (true, 0)], [(true, 0)]) := by decide +kernel
example : ¬ Valid (⟨1⟩, [], [(false, 1)]) := by decide +kernel
example : ¬ Valid (⟨1⟩, [], [(true, 0)]) := by decide +kernel
example : Valid (⟨0⟩, [], []) := by decide +kernel
example : EncodedBooleanCircuit.Gate.decode (3, []) = none := by decide +kernel
example : EncodedBooleanCircuit.Gate.decode (1, [(false, 0)]) = none := by decide +kernel

theorem circuit_roundtrip (c : Circuit) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode c) = some c := by simp

example : EndOfLinePromise (one1, zero1) := by decide +kernel
example : EndOfLineSolution (one1, zero1) [true] := by decide +kernel
example : ¬ EndOfLineSolution (one1, zero1) [false] := by decide +kernel
example : ¬ EndOfLineSolution (one1, zero1) [] := by decide +kernel
example : ¬ EndOfLinePromise (id1, id1) := by decide +kernel
example : EndOfLinePromise (not1, id1) := by decide +kernel
example : EndOfLineSolution (not1, id1) [false] := by decide +kernel
example : EndOfLinePromise (source2, pred2) := by decide +kernel
example : EndOfLineSolution (source2, pred2) [false, true] := by decide +kernel
example : eval pred2 (eval source2 [false, true]) = [false, true] := by decide +kernel
example : eval source2 (eval pred2 [false, true]) ≠ [false, true] := by decide +kernel

example : bitValue [] = 0 := by decide +kernel
example : bitValue [false] = 0 := by decide +kernel
example : bitValue [true] = 1 := by decide +kernel
example : bitValue [true, false, false] = 1 := by decide +kernel
example : bitValue [false, true, false] = 2 := by decide +kernel
example : bitValue [true, true, true] = 7 := by decide +kernel
example : cost id1 (fun _ : Fin 1 => true) = 2 := by decide +kernel
example : FlipSolution id1 [false] := by decide +kernel
example : ¬ FlipSolution id1 [true] := by decide +kernel
example : FlipSolution not1 [true] := by decide +kernel
example : ¬ FlipSolution not1 [] := by decide +kernel
example : FlipSolution zero1 [true] := by decide +kernel
example : FlipSolution (⟨0⟩, [], []) [] := by decide +kernel
example : FlipSolution (⟨1⟩, [.not (false, 0)], [(false, 0), (true, 0)]) [true] := by
  decide +kernel

example : transversals [] = {∅} := by decide +kernel
example : transversals [[]] = ∅ := by decide +kernel
example : transversals [[0]] = {{0}} := by decide +kernel
example : transversals [[0, 1]] = {{0}, {1}} := by decide +kernel
example : transversals [[0], [1]] = {{0, 1}} := by decide +kernel
example : transversals [[0, 1], [1, 2]] = {{1}, {0, 2}} := by decide +kernel
example : MinimalTransversal [[0, 1], [1, 2]] {0, 2} := by decide +kernel
example : ¬ MinimalTransversal [[0, 1], [1, 2]] {0, 1, 2} := by decide +kernel
example : transversals [[1000000, 2], [2]] = {{2}} := by decide +kernel
example : transversals [[0, 0], [0]] = {{0}} := by decide +kernel
example : ¬ MinimalTransversal [[0]] {0, 9} := by decide +kernel

theorem finite_set_roundtrip (s : Finset ℕ) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode s) = some s := by simp

theorem all_endOfLine_instances_have_answers (c : EndOfLineInput) (h : EndOfLinePromise c) :
    ∃ bs, EndOfLineSolution c bs := endOfLine_total c h

theorem all_flip_instances_have_answers (c : Circuit) : ∃ bs, FlipSolution c bs := flip_total c

theorem counting_support_bound (f : Computability.BooleanSatisfiability.Formula) :
    modelCount f ≤ 2 ^ (Computability.BooleanSatisfiability.support f).card := modelCount_le f

end SearchCountingTest
