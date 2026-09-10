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
import FormalConjecturesForMathlib.Computability.NumberTheoryProblems
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

/-!
# Number-theoretic boundary and semantic tests

These kernel proofs test positive versus nonnegative solutions, strict bounds,
Jacobi-one nonsquares, hidden RSA factors, nonunit ciphertexts, primitive generators,
and canonical search outputs. Runtime guards exercise only exhaustive reference checks.
-/

namespace NumberTheoryProblems.Test

open ComplexityTheory

-- Positive parameters, a strict upper bound, and a strictly positive root.
example : BoundedQuadraticCongruence (1, 3, 2) := by decide
example : ¬ BoundedQuadraticCongruence (1, 3, 1) := by decide
example : BoundedQuadraticCongruence (4, 7, 3) := by decide
example : ¬ BoundedQuadraticCongruence (4, 7, 2) := by decide
example : ¬ BoundedQuadraticCongruence (3, 3, 2) := by decide
example : BoundedQuadraticCongruence (3, 3, 4) := by decide
example : ¬ BoundedQuadraticCongruence (0, 3, 4) := by decide
example : ¬ BoundedQuadraticCongruence (1, 0, 4) := by decide
example : ¬ BoundedQuadraticCongruence (1, 3, 0) := by decide
example : BoundedQuadraticCongruence (1, 1, 2) := by decide

-- The source demands x > 0 AND y > 0, not merely nonnegative solutions.
example : BinaryQuadraticDiophantine (1, 1, 2) := by decide
example : ¬ BinaryQuadraticDiophantine (1, 1, 1) := by decide
example : BinaryQuadraticDiophantine (2, 3, 5) := by decide
example : ¬ BinaryQuadraticDiophantine (2, 3, 3) := by decide
example : ¬ BinaryQuadraticDiophantine (2, 3, 2) := by decide
example : BinaryQuadraticDiophantine (2, 3, 11) := by decide
example : ¬ BinaryQuadraticDiophantine (0, 1, 1) := by decide
example : ¬ BinaryQuadraticDiophantine (1, 0, 1) := by decide
example : ¬ BinaryQuadraticDiophantine (1, 1, 0) := by decide
example : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 2 * x ^ 2 + 3 * y = 11 :=
  (binaryQuadraticDiophantine_iff (2, 3, 11)).mp (by decide) |>.2.2.2

-- Both answers occur under the Jacobi-one promise at the same composite modulus.
theorem residue_yes_promise : ResiduosityPromise (15, 4) := by
  norm_num [ResiduosityPromise]
theorem residue_no_promise : ResiduosityPromise (15, 2) := by
  norm_num [ResiduosityPromise]
example : IsQuadraticResidue (15, 4) := by decide
example : ¬ IsQuadraticResidue (15, 2) := by decide
example : IsSquare (4 : ZMod 15) :=
  (isQuadraticResidue_iff (15, 4) (by decide)).mp (by decide)
example : ¬ IsSquare (2 : ZMod 15) := by
  intro h
  have hn : ¬ IsQuadraticResidue (15, 2) := by decide
  apply hn
  apply (isQuadraticResidue_iff (15, 2) (by decide)).mpr
  simpa using h
example : ResiduosityPromise (15, -11) := by norm_num [ResiduosityPromise]
example : IsQuadraticResidue (15, -11) := by decide
example : ResiduosityPromise (9, 2) := by norm_num [ResiduosityPromise]
example : ¬ IsQuadraticResidue (9, 2) := by decide
example : ¬ ResiduosityPromise (0, 1) := by norm_num [ResiduosityPromise]
example : ¬ ResiduosityPromise (1, 1) := by norm_num [ResiduosityPromise]
example : ¬ ResiduosityPromise (5, 4) := by norm_num [ResiduosityPromise]
example : ¬ ResiduosityPromise (6, 1) := by norm_num [ResiduosityPromise]
example : ¬ ResiduosityPromise (15, 3) := by norm_num [ResiduosityPromise]
example : ¬ ResiduosityPromise (15, 0) := by norm_num [ResiduosityPromise]
example : IsQuadraticResidue (15, 0) := by decide
example : (4 : ℤ).gcd 15 = 1 := residue_yes_promise.coprime

-- Valid RSA includes e = 1, negative ciphertext representatives, zero and nonunits.
theorem rsa_valid : RSAPromise (15, 3, 8) := by decide
example : RSAOutput (15, 3, 8) 2 := by decide
example : ¬ RSAOutput (15, 3, 8) 3 := by decide
example : ¬ RSAOutput (15, 3, 8) 17 := by decide
example : RSAPromise (15, 1, 7) := by decide
example : RSAOutput (15, 1, 7) 7 := by decide
example : RSAPromise (15, 3, -7) := by decide
example : RSAOutput (15, 3, -7) 2 := by decide
example : RSAOutput (15, 3, 0) 0 := by decide
example : RSAOutput (15, 3, 3) 12 := by decide
example : ¬ RSAPromise (15, 0, 8) := by decide
example : ¬ RSAPromise (15, 2, 8) := by decide
example : ¬ RSAPromise (9, 5, 1) := by decide
example : ¬ RSAPromise (10, 3, 1) := by decide
example : ¬ RSAPromise (7, 5, 1) := by decide
example : ¬ RSAPromise (0, 1, 1) := by decide
example : ¬ RSAPromise (1, 1, 1) := by decide
example : ∃! m, RSAOutput (15, 3, 8) m := existsUnique_rsaOutput _ rsa_valid
example : ∃! m, RSAOutput (15, 3, 3) m := existsUnique_rsaOutput _ (by decide)

-- Prime-field generators, p = 2, logarithm zero, and the strict upper exponent bound.
theorem discrete_log_valid : DiscreteLogarithmPromise (7, 3, 5) := by decide
example : DiscreteLogarithmOutput (7, 3, 5) 5 := by decide
example : ¬ DiscreteLogarithmOutput (7, 3, 5) 11 := by decide
example : DiscreteLogarithmPromise (7, 3, 1) := by decide
example : DiscreteLogarithmOutput (7, 3, 1) 0 := by decide
example : ¬ DiscreteLogarithmOutput (7, 3, 1) 6 := by decide
example : DiscreteLogarithmPromise (2, 1, 1) := by decide
example : DiscreteLogarithmOutput (2, 1, 1) 0 := by decide
example : ¬ DiscreteLogarithmPromise (7, 2, 4) := by decide
example : ¬ DiscreteLogarithmPromise (7, 1, 1) := by decide
example : ¬ DiscreteLogarithmPromise (9, 2, 4) := by decide
example : ¬ DiscreteLogarithmPromise (7, 0, 1) := by decide
example : ¬ DiscreteLogarithmPromise (7, 3, 0) := by decide
example : ¬ DiscreteLogarithmPromise (7, 7, 1) := by decide
example : ¬ DiscreteLogarithmPromise (7, 3, 7) := by decide
example : ¬ DiscreteLogarithmPromise (0, 0, 0) := by decide
example : ¬ DiscreteLogarithmPromise (1, 0, 0) := by decide
example : IsPrimitiveRoot (3 : ZMod 7) 6 :=
  (discreteLogarithmPromise_iff (7, 3, 5)).mp discrete_log_valid |>.2.2.2.2.2
example : ∃! x, DiscreteLogarithmOutput (7, 3, 5) x :=
  existsUnique_discreteLogarithmOutput _ discrete_log_valid

-- Binary input/output encodings and the genuine TM2-based solver interface.
example (i : QuadraticInput) : BitstringEncoding.bitDecode (BitstringEncoding.bitEncode i) = some i :=
  BitstringEncoding.bitDecode_bitEncode i
example (i : ResiduosityInput) : BitstringEncoding.bitDecode (BitstringEncoding.bitEncode i) = some i :=
  BitstringEncoding.bitDecode_bitEncode i
example (i : RSAInput) : BitstringEncoding.bitDecode (BitstringEncoding.bitEncode i) = some i :=
  BitstringEncoding.bitDecode_bitEncode i
example (i : DiscreteLogarithmInput) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode i) = some i :=
  BitstringEncoding.bitDecode_bitEncode i
example : HasPolyTimeSolver (fun _ : ℕ ↦ True) (fun x y : ℕ ↦ y = x) :=
  isPolyTime_id.hasPolyTimeSolver _
example : HasPolyTimePromiseDecider (fun _ : Bool ↦ True) (fun b ↦ b = true) :=
  (hasPolyTimePromiseDecider_true _).mpr isPolyTime_id.hasPolyTimeDecider
example : HasPolyTimeSolver (fun _ : ℕ ↦ False) (fun _ _ : ℕ ↦ False) :=
  (isPolyTime_id.hasPolyTimeSolver (fun _ : ℕ ↦ True)).mono
    (fun _ h ↦ h.elim) (fun _ _ h _ ↦ h.elim)
example : ¬ HasPolyTimeSolver (fun _ : ℕ ↦ True) (fun _ _ : ℕ ↦ False) := by
  rintro ⟨f, _, h⟩
  exact h 0 trivial

#guard decide (BoundedQuadraticCongruence (4, 7, 3)) &&
  !(decide (BoundedQuadraticCongruence (4, 7, 2)))
#guard decide (ResiduosityPromise (15, 2)) && !(decide (IsQuadraticResidue (15, 2)))
#guard decide (RSAPromise (15, 3, -7)) && decide (RSAOutput (15, 3, -7) 2)
#guard decide (DiscreteLogarithmPromise (7, 3, 1)) &&
  decide (DiscreteLogarithmOutput (7, 3, 1) 0)

end NumberTheoryProblems.Test
