/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.NumberTheory.NumberField.Basic
public import FormalConjecturesForMathlib.Algebra.QuadraticAlgebra.Basic
public import FormalConjecturesForMathlib.Algebra.QuadraticAlgebra.Instances

public section

open Algebra (IsQuadraticExtension)
open Module NumberField

/-- Any `QuadraticAlgebra ℚ a b` that is a field is automatically a quadratic extension
of `ℚ`, i.e., a degree-2 extension. Combined with `IsQuadraticField.instNumberField`,
this gives `NumberField (QuadraticAlgebra ℚ a b)` for free. -/
instance QuadraticAlgebra.instIsQuadraticExtension (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

/-- A quadratic field is a number field: it has characteristic zero
and is finite-dimensional over `ℚ`. -/
instance Algebra.IsQuadraticExtension.to_numberField (K : Type*) [Field K] [CharZero K]
    [IsQuadraticExtension ℚ K] : NumberField K where
  to_finiteDimensional := .of_finrank_pos <| by grind [IsQuadraticExtension.finrank_eq_two]
