import FormalConjectures.ForMathlib.LinearAlgebra.GeneralLinearGroup

open Matrix
open scoped MatrixGroups

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/-- The group of invertible diagonal matrices with determinant 1. -/
def Matrix.SpecialLinearGroup.diagonalSubgroup : Subgroup (SpecialLinearGroup n R) :=
  (Matrix.GeneralLinearGroup.diagonalSubgroup n R).comap Matrix.SpecialLinearGroup.toGL
