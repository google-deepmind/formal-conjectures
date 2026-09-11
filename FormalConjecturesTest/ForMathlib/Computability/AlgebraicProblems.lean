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
import FormalConjecturesForMathlib.Computability.AlgebraicProblems
import FormalConjecturesForMathlib.Computability.DecisionProblems
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring

/-!
# Boundary and semantic tests for algebraic problems

All examples are kernel-checked. Tests cover shared gates, malformed references,
constant-free syntax, exact irrational comparisons, determinant cancellations,
and the distinction between permanent and determinant.
-/

namespace AlgebraicProblemsTest

open ArithmeticCircuit AlgebraicProblems BitstringEncoding

abbrev IC := Program ℕ ℤ

example (c : IC) : bitDecode (bitEncode c) = some c := bitDecode_bitEncode c
example (m : LinearMatrix) : bitDecode (bitEncode m) = some m := bitDecode_bitEncode m
example (x : List ℕ × ℤ) : bitDecode (bitEncode x) = some x := bitDecode_bitEncode x
example (i : ℕ) : Gate.decode (Gate.code (.input i : Gate ℕ ℤ)) = some (.input i) := rfl
example (z : ℤ) : Gate.decode (Gate.code (.constant z : Gate ℕ ℤ)) = some (.constant z) := rfl
example (i j : ℕ) : Gate.decode (Gate.code (.add i j : Gate ℕ ℤ)) = some (.add i j) := rfl
example (i j : ℕ) : Gate.decode (Gate.code (.sub i j : Gate ℕ ℤ)) = some (.sub i j) := rfl
example (i j : ℕ) : Gate.decode (Gate.code (.mul i j : Gate ℕ ℤ)) = some (.mul i j) := rfl
example : Gate.decode (99, [], [], []) = (none : Option (Gate ℕ ℤ)) := rfl
example : Gate.decode (2, [], [], [0]) = (none : Option (Gate ℕ ℤ)) := rfl
example : Gate.decode (0, [3], [1], []) = (none : Option (Gate ℕ ℤ)) := rfl
example : Gate.decode (4, [], [], [0, 1, 2]) = (none : Option (Gate ℕ ℤ)) := rfl

example : run ([] : IC) (fun _ => 0) id = none := rfl
example : run ([.constant (-19)] : IC) (fun _ => 0) id = some (-19) := rfl
example : run ([.input 1000000] : IC) (fun i => (i : ℤ)) id = some 1000000 := rfl
example : run ([.add 0 0] : IC) (fun _ => 0) id = none := rfl
example : run ([.constant 1, .mul 1 0] : IC) (fun _ => 0) id = none := rfl
example : run ([.constant 1, .add 0 5, .constant 0] : IC) (fun _ => 0) id = none := rfl
example : run ([.constant 1, .sub 0 0] : IC) (fun _ => 0) id = some 0 := rfl
example : run ([.constant 1, .add 0 0, .mul 1 1] : IC) (fun _ => 0) id = some 4 := rfl
example : run ([.constant 1, .constant 0] : IC) (fun _ => 0) id = some 0 := rfl

def repeatedSquaring : IC := [.input 0, .mul 0 0, .mul 1 1, .mul 2 2, .mul 3 3]

example : repeatedSquaring.length = 5 := rfl
example : edgeSize repeatedSquaring = 8 := rfl
example : run repeatedSquaring (fun _ => 2) id = some 65536 := by decide
theorem repeatedSquaring_polynomial :
    polynomial repeatedSquaring = some (MvPolynomial.X 0 ^ 16 : MvPolynomial ℕ ℤ) := by
  simp [polynomial, repeatedSquaring, run, evalFrom, Gate.eval]
  ring

example : polynomial ([] : IC) = none := rfl
example : ¬ IsArithmeticIdentity [] := by simp [IsArithmeticIdentity, polynomial, run, evalFrom]
example : IsArithmeticIdentity [.constant 0] := by
  rw [arithmeticIdentity_iff]
  constructor
  · decide
  · intro v; simp [run, evalFrom, Gate.eval]
example : IsArithmeticIdentity [.input 0, .sub 0 0] := by
  rw [arithmeticIdentity_iff]
  constructor
  · decide
  · intro v; simp [run, evalFrom, Gate.eval]
example : ¬ IsArithmeticIdentity [.constant 2, .sub 0 0] := by
  simp [IsArithmeticIdentity, constantFreeGate]

/-- A nontrivial identity with shared subcircuits. -/
theorem square_expansion_identity :
    IsArithmeticIdentity [.input 0, .input 1, .add 0 1, .mul 2 2,
      .mul 0 0, .mul 1 1, .mul 0 1, .add 6 6, .add 4 5, .add 8 7, .sub 3 9] := by
  rw [arithmeticIdentity_iff]
  constructor
  · decide
  · intro v
    simp [run, evalFrom, Gate.eval]
    ring

/-- Zero at 0 and 1 is not polynomial identity over the integers. -/
theorem integer_not_boolean_identity :
    ¬ IsArithmeticIdentity [.input 0, .mul 0 0, .sub 1 0] := by
  intro h
  have hv := ((arithmeticIdentity_iff _).mp h).2 (fun _ => 2)
  norm_num [run, evalFrom, Gate.eval] at hv

example : ¬ IsPositiveSLP [] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant 0] := by rw [← positiveSLP_eq_true]; decide
example : IsPositiveSLP [.constant 1] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant 2] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant (-1)] := by rw [← positiveSLP_eq_true]; decide
example : IsPositiveSLP [.constant 1, .add 0 0] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant 1, .sub 0 0] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant 0, .constant 1, .sub 0 1] := by
  rw [← positiveSLP_eq_true]; decide
example : IsPositiveSLP [.constant 0, .constant 1, .sub 0 1, .mul 2 2] := by
  rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.input 0, .constant 1] := by rw [← positiveSLP_eq_true]; decide
example : ¬ IsPositiveSLP [.constant 1, .mul 0 2] := by rw [← positiveSLP_eq_true]; decide

example : SumSquareRootsAtLeast ([], 0) := by norm_num [SumSquareRootsAtLeast]
example : SumSquareRootsAtLeast ([], -1) := by norm_num [SumSquareRootsAtLeast]
example : ¬ SumSquareRootsAtLeast ([], 1) := by norm_num [SumSquareRootsAtLeast]
example : SumSquareRootsAtLeast ([0, 1, 4, 9], 6) := by norm_num [SumSquareRootsAtLeast]
example : ¬ SumSquareRootsAtLeast ([0, 1, 4, 9], 7) := by norm_num [SumSquareRootsAtLeast]
example : SumSquareRootsAtLeast ([2], 1) := by
  norm_num [SumSquareRootsAtLeast]
example : ¬ SumSquareRootsAtLeast ([2], 2) := by
  norm_num [SumSquareRootsAtLeast]
example : SumSquareRootsAtLeast ([2, 2], 2) := by
  change (2 : ℝ) ≤ Real.sqrt 2 + (Real.sqrt 2 + 0)
  linarith [Real.one_lt_sqrt_two]
example : ¬ SumSquareRootsAtLeast ([2, 2], 3) := by
  have h : Real.sqrt 2 < (3 : ℝ) / 2 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  change ¬ ((3 : ℝ) ≤ Real.sqrt 2 + (Real.sqrt 2 + 0))
  linarith

example : Square [] := by simp [Square]
example : Square [[[]]] := by simp [Square]
example : ¬ Square [[]] := by simp [Square]
example : ¬ Square [[[], []], [[]]] := by simp [Square]
example : linearValue (fun i => (i : ℤ)) [(3, 5), (3, -5), (2, 7)] = 14 := rfl
example : linearPolynomial [(3, 5), (3, -5)] = 0 := by simp [linearPolynomial]
example : SymbolicNonsingular [] := by
  simp [SymbolicNonsingular, Square, Matrix.det_isEmpty]
example : ¬ SymbolicNonsingular [[]] := by simp [SymbolicNonsingular, Square]
example : ¬ SymbolicNonsingular [[[]]] := by
  simp [SymbolicNonsingular, polynomialMatrix, Matrix.det_unique, linearPolynomial]
example : SymbolicNonsingular [[[(0, 1)]]] := by
  rw [symbolicNonsingular_iff]
  refine ⟨by simp [Square], fun _ => 1, ?_⟩
  change Matrix.det !![(1 : ℤ)] ≠ 0
  norm_num [Matrix.det_unique]
example : ¬ SymbolicNonsingular [[[(0, 1), (0, -1)]]] := by
  simp [SymbolicNonsingular, polynomialMatrix, Matrix.det_unique, linearPolynomial]

/-- The determinant distinguishes cancellation from permanent addition. -/
theorem repeated_rows_singular :
    ¬ SymbolicNonsingular [[[(0, 1)], [(1, 1)]], [[(0, 1)], [(1, 1)]]] := by
  simp [SymbolicNonsingular, polynomialMatrix, Matrix.det_fin_two, linearPolynomial, mul_comm]

example : SymbolicNonsingular [[[(0, 1)], []], [[], [(1, 1)]]] := by
  rw [symbolicNonsingular_iff]
  refine ⟨by simp [Square], fun _ => 1, ?_⟩
  change Matrix.det !![(1 : ℤ), 0; 0, 1] ≠ 0
  norm_num [Matrix.det_fin_two]

example : permanentPolynomial 0 = 1 := Matrix.permanent_isEmpty
example : permanentPolynomial 1 = MvPolynomial.X (0, 0) := by
  simp [permanentPolynomial, Matrix.mvPolynomialX, Fin.default_eq_zero]

theorem permanent_two : permanentPolynomial 2 =
    MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) +
      MvPolynomial.X (1, 0) * MvPolynomial.X (0, 1) := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [permanentPolynomial, Matrix.permanent, h,
    Finset.sum_pair (show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide)]
  simp [Fin.prod_univ_two, Matrix.mvPolynomialX]

example : polynomial ([.input (0, 0), .input (1, 1), .input (1, 0), .input (0, 1),
    .mul 0 1, .mul 2 3, .add 4 5] : Program (Fin 2 × Fin 2) ℚ) =
      some (permanentPolynomial 2) := by
  simp [permanent_two, polynomial, run, evalFrom, Gate.eval]

example : Matrix.permanent !![(1 : ℚ), 2; 3, 4] = 10 := by decide +kernel
example : Matrix.det !![(1 : ℚ), 2; 3, 4] = -2 := by norm_num [Matrix.det_fin_two]
example : polynomial ([.constant 1] : Program (Fin 0 × Fin 0) ℚ) =
    some (permanentPolynomial 0) := by
  simp [polynomial, run, evalFrom, Gate.eval, permanentPolynomial, Matrix.permanent_isEmpty]
example : polynomial ([.input (0, 0)] : Program (Fin 1 × Fin 1) ℚ) =
    some (permanentPolynomial 1) := by
  simp [polynomial, run, evalFrom, Gate.eval, permanentPolynomial,
    Matrix.mvPolynomialX, Fin.default_eq_zero]
example : edgeSize ([.constant (123456789 / 17)] : Program ℕ ℚ) = 0 := rfl
example : edgeSize ([.input 0, .mul 0 0, .add 1 1] : IC) = 4 := rfl
example : ([.constant (-1), .mul 0 0] : Program ℕ ℚ).all addMulGate = true := rfl
example : ([.constant 1, .sub 0 0] : IC).all addMulGate = false := rfl
example : ComplexityTheory.HasPolyTimeDecider (fun b : Bool => b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

#guard positiveSLP [.constant 1, .add 0 0, .mul 1 1]
#guard !positiveSLP [.constant 1, .sub 0 0]
#guard run repeatedSquaring (fun _ => 2) id == some 65536
#guard (bitEncode ([.input 1000000] : IC)).length < 1000

end AlgebraicProblemsTest
