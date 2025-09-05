/-
Copyright 2024 The Formal Conjectures Authors.

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
