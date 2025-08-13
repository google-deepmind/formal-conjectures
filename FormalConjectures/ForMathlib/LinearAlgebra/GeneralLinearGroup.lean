import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

open Matrix
open scoped MatrixGroups

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/-- The multiplicative group homomorphism `(Rˣ)ⁿ →* GL(n, R)` given by mapping a vector `x` to
`Matrix.diagonal x`. -/
def Matrix.GeneralLinearGroup.diagonalHom : (n → Rˣ) →* GeneralLinearGroup n R where
  toFun := fun d ↦ ⟨Matrix.diagonal (fun i ↦ d i), Matrix.diagonal (fun i ↦ (d i).inv), by simp, by simp⟩
  map_mul' x y := by ext; simp [-mul_diagonal, -diagonal_mul]
  map_one' := by ext; simp

/-- The group of invertible diagonal matrices. -/
def Matrix.GeneralLinearGroup.diagonalSubgroup : Subgroup (GeneralLinearGroup n R) :=
  Subgroup.map (Matrix.GeneralLinearGroup.diagonalHom n R) ⊤
