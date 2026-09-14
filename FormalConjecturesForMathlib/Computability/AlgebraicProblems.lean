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

public import FormalConjecturesForMathlib.Computability.ArithmeticCircuit
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Algebraic decision problems and permanent circuit families

The uniform inputs below use finite binary encodings. Circuits are explicit DAGs,
not expression trees or expanded coefficient lists. The root-sum predicate uses exact
real square roots, including equality at the threshold. The permanent family instead
uses the nonuniform algebraic model: arbitrary rational constants and edge count.

References:
* Allender et al., *On the Complexity of Numerical Analysis*, §§1.4 and 2,
  https://people.cs.rutgers.edu/~allender/papers/slp.pdf.
* Ivanyos–Karpinski–Qiao–Santha, *Generalized Wong sequences and their applications
  to Edmonds' problems*, §1, https://arxiv.org/abs/1307.6429v2.
* Shpilka–Yehudayoff, *Arithmetic circuits: A survey of recent results and open
  questions*, Definitions 1.1–1.2, §1.2, https://www.cs.tau.ac.il/~shpilka/publications/SY10.pdf.
-/

@[expose] public section

namespace AlgebraicProblems

open ArithmeticCircuit

/-- Constant-free arithmetic circuit syntax: the permitted constants are exactly 0 and 1. -/
def constantFreeGate : Gate ℕ ℤ → Bool
  | .constant z => z == 0 || z == 1
  | _ => true

/-- Variable-free constant-free SLP syntax for PosSLP. -/
def closedGate : Gate ℕ ℤ → Bool
  | .input _ => false
  | g => constantFreeGate g

/-- ACIT for division-free straight-line programs over the integers, with no degree bound. -/
def IsArithmeticIdentity (c : Program ℕ ℤ) : Prop :=
  c.all constantFreeGate = true ∧ polynomial c = some 0

/-- PosSLP: a valid closed program over 0,1,+,−,× has strictly positive integer output. -/
def IsPositiveSLP (c : Program ℕ ℤ) : Prop :=
  c.all closedGate = true ∧ ∃ z : ℤ, run c (fun _ => 0) id = some z ∧ 0 < z

/-- An exact reference decider for PosSLP, without a polynomial running-time claim. -/
def positiveSLP (c : Program ℕ ℤ) : Bool :=
  c.all closedGate && match run c (fun _ => 0) id with
    | none => false
    | some z => decide (0 < z)

theorem positiveSLP_eq_true (c : Program ℕ ℤ) :
    positiveSLP c = true ↔ IsPositiveSLP c := by
  cases h : run c (fun _ => (0 : ℤ)) id <;> simp [positiveSLP, IsPositiveSLP, h]

theorem arithmeticIdentity_iff (c : Program ℕ ℤ) :
    IsArithmeticIdentity c ↔
      c.all constantFreeGate = true ∧ ∀ v : ℕ → ℤ, run c v id = some 0 := by
  rw [IsArithmeticIdentity, polynomial_eq_zero_iff]

/-- Exact sum-of-square-roots comparison. Radicands are nonnegative integers;
the threshold is an arbitrary signed integer. -/
def SumSquareRootsAtLeast (input : List ℕ × ℤ) : Prop :=
  (input.2 : ℝ) ≤ (input.1.map fun d => Real.sqrt (d : ℝ)).sum

/-- A sparse homogeneous linear form: a list of variable-index/coefficient pairs.
Repeated indices contribute additively, including cancellation. -/
abbrev LinearForm := List (ℕ × ℤ)

/-- A matrix explicitly represented by all its rows. -/
abbrev LinearMatrix := List (List LinearForm)

/-- No padding convention turns a ragged matrix into a valid square input. -/
def Square (m : LinearMatrix) : Prop :=
  ∀ row ∈ m, row.length = m.length

/-- The actual polynomial denoted by a homogeneous linear form. -/
noncomputable def linearPolynomial (l : LinearForm) : MvPolynomial ℕ ℤ :=
  (l.map fun t => MvPolynomial.C t.2 * MvPolynomial.X t.1).sum

/-- Evaluate a homogeneous linear form exactly. -/
def linearValue (v : ℕ → ℤ) (l : LinearForm) : ℤ :=
  (l.map fun t => t.2 * v t.1).sum

theorem eval_linearPolynomial (v : ℕ → ℤ) (l : LinearForm) :
    MvPolynomial.eval v (linearPolynomial l) = linearValue v l := by
  induction l with
  | nil => simp [linearPolynomial, linearValue]
  | cons t l ih => simp_all [linearPolynomial, linearValue]

/-- The row representation interpreted as a square polynomial matrix.
Missing entries default to zero only here; SDIT separately requires `Square`. -/
noncomputable def polynomialMatrix (m : LinearMatrix) :
    Matrix (Fin m.length) (Fin m.length) (MvPolynomial ℕ ℤ) :=
  fun i j => linearPolynomial ((m[i]).getD j [])

/-- The same row representation evaluated at an integer assignment. -/
def valueMatrix (m : LinearMatrix) (v : ℕ → ℤ) :
    Matrix (Fin m.length) (Fin m.length) ℤ :=
  fun i j => linearValue v ((m[i]).getD j [])

theorem eval_determinant (m : LinearMatrix) (v : ℕ → ℤ) :
    MvPolynomial.eval v (Matrix.det (polynomialMatrix m)) =
      Matrix.det (valueMatrix m v) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact eval_linearPolynomial v _

/-- SDIT in the nonsingularity orientation used in §1 of the Wong-sequences paper:
the determinant of a square matrix of homogeneous integer linear forms is not zero. -/
def SymbolicNonsingular (m : LinearMatrix) : Prop :=
  Square m ∧ Matrix.det (polynomialMatrix m) ≠ 0

/-- Polynomial nonsingularity is equivalent to some integer specialization being nonsingular. -/
theorem symbolicNonsingular_iff (m : LinearMatrix) :
    SymbolicNonsingular m ↔ Square m ∧ ∃ v : ℕ → ℤ, Matrix.det (valueMatrix m v) ≠ 0 := by
  classical
  simp only [SymbolicNonsingular, ne_eq, MvPolynomial.funext_iff,
    map_zero, eval_determinant, not_forall]

/-- The permanent polynomial of the generic n-by-n matrix over the rationals. -/
noncomputable def permanentPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ :=
  Matrix.permanent (Matrix.mvPolynomialX (Fin n) (Fin n) ℚ)

theorem eval_permanentPolynomial (n : ℕ) (v : Fin n × Fin n → ℚ) :
    MvPolynomial.eval v (permanentPolynomial n) =
      Matrix.permanent (fun i j => v (i, j)) := by
  simp [permanentPolynomial, Matrix.permanent, Matrix.mvPolynomialX]

/-- The +,× basis of Shpilka–Yehudayoff Definition 1.1. Subtraction is not used
in the permanent circuit family, although it is available in the shared SLP model. -/
def addMulGate {σ R : Type} : Gate σ R → Bool
  | .sub _ _ => false
  | _ => true

/-- Number of incoming edges at a gate, counting a repeated operand twice. -/
def gateEdges {σ R : Type} : Gate σ R → ℕ
  | .input _ | .constant _ => 0
  | .add _ _ | .sub _ _ | .mul _ _ => 2

/-- Circuit size is edge count, as in Definition 1.1 of the survey. -/
def edgeSize {σ R : Type} (c : Program σ R) : ℕ :=
  (c.map gateEdges).sum

/-- A nonuniform polynomial-size circuit family for the permanent over ℚ.
The constants C,d are uniform in n; the circuits and their rational constants need
not be generated by an algorithm. Rational bit lengths are not charged in this model. -/
def HasPolynomialSizePermanentCircuits : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, ∃ c : Program (Fin n × Fin n) ℚ,
    c.all addMulGate = true ∧
    edgeSize c ≤ C * (n + 1) ^ d ∧ polynomial c = some (permanentPolynomial n)

end AlgebraicProblems
