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
import FormalConjecturesForMathlib.Computability.AutomataProblems

/-!
# Boundary and semantic tests for string and automata problems

Examples use kernel-checked decision procedures, not native evaluation.
The guarded evaluations separately test the executable reference decisions.
-/

namespace Computability.StringAutomataProblems.Test

open StringProblems AutomataProblems

-- Alphabet membership, repetitions, and typed-word round trips.
example : WordIn 0 [] := by decide
example : ¬ WordIn 0 [0] := by decide
example : WordIn 3 [2, 0, 2] := by decide
example : ¬ WordIn 3 [3] := by decide
example : StringsIn 0 [[], []] := by decide
example : ¬ StringsIn 0 [[0]] := by decide
example : wordValues (typedWord [2, 0, 2] (by decide : WordIn 3 _)) = [2, 0, 2] := by
  simp

-- Supersequence: order matters, multiplicity matters, and unused alphabet symbols are allowed.
example : CommonSupersequence (2, [[0, 1], [1, 0]], 3) := by decide
example : ¬ CommonSupersequence (2, [[0, 1], [1, 0]], 2) := by decide
example : CommonSupersequence (3, [[0, 2], [0, 1, 2]], 3) := by decide
example : CommonSupersequence (3, [[0, 1], [0, 1]], 2) := by decide
example : CommonSupersequence (1, [[0, 0], [0]], 2) := by decide
example : ¬ CommonSupersequence (1, [[0, 0]], 1) := by decide
example : CommonSupersequence (0, [], 1) := by decide
example : CommonSupersequence (0, [[], []], 1) := by decide
example : ¬ CommonSupersequence (2, [], 0) := by decide
example : ¬ CommonSupersequence (2, [[2]], 3) := by decide
example : CommonSupersequence (2, [[], [1]], 1) := by decide

-- Superstring: overlap is allowed, arbitrary deletion is not.
example : CommonSuperstring (3, [[0, 1], [1, 2]], 3) := by decide
example : ¬ CommonSuperstring (3, [[0, 1], [1, 2]], 2) := by decide
example : ¬ CommonSuperstring (3, [[0, 2], [0, 1, 2]], 3) := by decide
example : CommonSuperstring (2, [[0, 1], [0, 1]], 2) := by decide
example : CommonSuperstring (1, [[0, 0], [0]], 2) := by decide
example : ¬ CommonSuperstring (1, [[0, 0]], 1) := by decide
example : CommonSuperstring (0, [], 1) := by decide
example : CommonSuperstring (0, [[], []], 1) := by decide
example : ¬ CommonSuperstring (2, [], 0) := by decide
example : ¬ CommonSuperstring (2, [[2]], 3) := by decide
example : CommonSuperstring (2, [[], [1]], 1) := by decide

-- Common subsequence: all input strings constrain the same word.
example : CommonSubsequence (3, [[0, 1, 2], [0, 2, 1], [0, 2]], 2) := by decide
example : ¬ CommonSubsequence (3, [[0, 1, 2], [0, 2, 1], [0, 2]], 3) := by decide
example : CommonSubsequence (2, [[0, 1], [1, 0]], 1) := by decide
example : ¬ CommonSubsequence (2, [[0, 1], [1, 0]], 2) := by decide
example : CommonSubsequence (2, [[0, 0], [0, 0]], 2) := by decide
example : ¬ CommonSubsequence (2, [[0, 0], [0]], 2) := by decide
example : ¬ CommonSubsequence (0, [], 1) := by decide
example : CommonSubsequence (2, [], 1) := by decide
example : ¬ CommonSubsequence (2, [], 0) := by decide
example : ¬ CommonSubsequence (2, [[2]], 1) := by decide
example : ¬ CommonSubsequence (2, [[], [1]], 1) := by decide

-- Finite enumeration includes the empty word even over an empty alphabet.
example : BoundedWord 0 (fun w : List (Fin 0) ↦ w = []) := by decide
example : ¬ BoundedWord 2 (fun w : List (Fin 0) ↦ 0 < w.length) := by decide
example (x : CommonInput) : CommonSubsequence x ↔
    StringsIn x.1 x.2.1 ∧ 0 < x.2.2 ∧
      ∃ w : List (Fin x.1), x.2.2 ≤ w.length ∧ ∀ s ∈ x.2.1, (wordValues w).Sublist s :=
  commonSubsequence_iff x

def allWords : Code := ([[0, 0]], 0, [true])
def noWords : Code := ([[0, 0]], 0, [false])
def endsZero : Code := ([[1, 0], [1, 0]], 0, [false, true])
def endsOne : Code := ([[0, 1], [0, 1]], 0, [false, true])
def oddLength : Code := ([[1], [0]], 0, [false, true])
def lengthTwoModThree : Code := ([[1], [2], [0]], 0, [false, false, true])

example : ValidCode 2 allWords := by decide
example : ¬ ValidCode 1 allWords := by decide
example : ¬ ValidCode 2 ([[0]], 0, [true]) := by decide
example : ¬ ValidCode 1 ([[1]], 0, [true]) := by decide
example : ¬ ValidCode 1 ([[0]], 1, [true]) := by decide
example : ¬ ValidCode 1 ([[0]], 0, []) := by decide
example : ¬ ValidCode 1 ([[0]], 0, [true, false]) := by decide
example : ¬ ValidCode 0 ([], 0, []) := by decide
example : ValidCode 0 ([[]], 0, [true]) := by decide

example : ([0, 1, 0] : List (Fin 2)) ∈
    (toDFA 2 endsZero (by decide)).accepts := by decide
example : ([0, 1] : List (Fin 2)) ∉
    (toDFA 2 endsZero (by decide)).accepts := by decide
example : ([] : List (Fin 2)) ∉
    (toDFA 2 endsZero (by decide)).accepts := by decide

example : DFAIntersection (0, []) := by decide
example : DFAIntersection (2, []) := by decide
example : DFAIntersection (2, [allWords, allWords]) := by decide
example : ¬ DFAIntersection (2, [allWords, noWords]) := by decide
example : DFAIntersection (2, [allWords, endsZero]) := by decide
example : ¬ DFAIntersection (2, [endsZero, endsOne]) := by decide
example : DFAIntersection (0, [([[]], 0, [true])]) := by decide
example : ¬ DFAIntersection (0, [([[]], 0, [false])]) := by decide
example : ¬ DFAIntersection (2, [allWords, ([[0]], 0, [true])]) := by decide
example : ¬ DFAIntersection (0, [([], 0, [])]) := by decide
example : DFAIntersection (1, [oddLength, lengthTwoModThree]) := by decide

-- The common witness may be longer than either individual state count.
example : ¬ BoundedWord 3 (fun w : List (Fin 1) ↦
    w ∈ (toDFA 1 oddLength (by decide)).accepts ∧
    w ∈ (toDFA 1 lengthTwoModThree (by decide)).accepts) := by decide
example : (List.replicate 5 (0 : Fin 1)) ∈
    (toDFA 1 oddLength (by decide)).accepts ∧
    (List.replicate 5 (0 : Fin 1)) ∈
    (toDFA 1 lengthTwoModThree (by decide)).accepts := by decide
example (x : IntersectionInput) (h : AllValid x) :
    DFAIntersection x ↔ ∃ w : List (Fin x.1),
      ∀ i : Fin x.2.length, w ∈ (toDFA x.1 x.2[i] (h i)).accepts :=
  dfaIntersection_iff x h

-- Inference: exact positive K, arbitrary initial/accepting states, samples only.
example : InferredDFA (0, [], [], 1) := by decide
example : InferredDFA (2, [], [], 1) := by decide
example : ¬ InferredDFA (2, [], [], 0) := by decide
example : InferredDFA (0, [[]], [], 1) := by decide
example : InferredDFA (0, [], [[]], 1) := by decide
example : ¬ InferredDFA (0, [[]], [[]], 1) := by decide
example : ¬ InferredDFA (2, [[0]], [[0]], 2) := by
  simp [InferredDFA, ValidSamples, StringsIn, WordIn, Consistent]
example : ¬ InferredDFA (2, [[0]], [[1]], 1) := by decide
example : InferredDFA (2, [[0]], [[1]], 2) := by decide
example : ¬ InferredDFA (2, [[2]], [], 2) := by decide
example : ¬ InferredDFA (2, [], [[2]], 2) := by decide
example : ¬ InferredDFA (0, [[0]], [], 1) := by decide
example : ¬ InferredDFA (1, [[]], [[0]], 1) := by decide
example : InferredDFA (1, [[]], [[0]], 2) := by decide
example : InferredDFA (1, [[0]], [[]], 2) := by decide
example : InferredDFA (1, [[0], [0]], [[]], 2) := by decide
example : InferredDFA (1, [[0]], [], 1) := by decide
example : InferredDFA (0, [[]], [], 3) := by decide

-- A sample-consistent DFA can accept unlisted strings and contain unreachable states.
def paddedAccept : Witness 1 3 := (fun q _ ↦ q, 0, fun _ ↦ true)
example : Consistent (1, [[0]], [], 3) (by decide) paddedAccept.toDFA := by decide
example : ([] : List (Fin 1)) ∈ paddedAccept.toDFA.accepts := by decide
example (w : List (Fin 1)) : paddedAccept.toDFA.eval w = 0 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton a w ih => simpa [paddedAccept, Witness.toDFA] using ih

example (m K : ℕ) (M : DFA (Fin m) (Fin K)) :
    ∃ c : Witness m K, c.toDFA = M := Witness.toDFA_surjective m K M
example (x : InferenceInput) (h : ValidSamples x) :
    InferredDFA x ↔ 0 < x.2.2.2 ∧
      ∃ M : DFA (Fin x.1) (Fin x.2.2.2), Consistent x h M :=
  inferredDFA_iff x h

-- The complexity predicate is inhabited by a real polynomial-time identity machine.
example : ComplexityTheory.HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

/-- info: [true, false, true] -/
#guard_msgs in
#eval [decide (CommonSupersequence (3, [[0, 2], [0, 1, 2]], 3)),
  decide (CommonSuperstring (3, [[0, 2], [0, 1, 2]], 3)),
  decide (CommonSubsequence (3, [[0, 1, 2], [0, 2]], 2))]

/-- info: [true, false, true, false] -/
#guard_msgs in
#eval [decide (DFAIntersection (1, [oddLength, lengthTwoModThree])),
  decide (DFAIntersection (2, [endsZero, endsOne])),
  decide (InferredDFA (2, [[0]], [[1]], 2)),
  decide (InferredDFA (2, [[0]], [[0]], 2))]

end Computability.StringAutomataProblems.Test
