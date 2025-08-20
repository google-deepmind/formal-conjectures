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


import FormalConjectures.ForMathlib.LinearAlgebra.GeneralLinearGroup

open Matrix
open scoped MatrixGroups

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

/-- The group of invertible diagonal matrices with determinant 1. -/
def Matrix.SpecialLinearGroup.diagonalSubgroup : Subgroup (SpecialLinearGroup n R) :=
  (Matrix.GeneralLinearGroup.diagonalSubgroup n R).comap Matrix.SpecialLinearGroup.toGL
