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

public import Mathlib.Data.Matrix.Basic

@[expose] public section

variable {n : ℕ}

open Finset

/--
A latin square of order `n` is an `n × n` matrix with entries in `Fin n` such that each symbol
appears exactly once in every row and exactly once in every column.
-/
structure LatinSquare (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) (Fin n)
  /-- Each row is a permutation of `Fin n`. -/
  row_injective : ∀ i, Function.Injective (mat i)
  /-- Each column is a permutation of `Fin n`. -/
  col_injective : ∀ j, Function.Injective (mat.transpose j)

/--
There are finitely many latin squares of order `n`, since each is determined by a matrix in
the finite type `Matrix (Fin n) (Fin n) (Fin n)`. This is useful for defining the maximum number of
transversals over all latin squares of order `n`.
-/
instance : Fintype (LatinSquare n) :=
  Fintype.ofEquiv
    {mat : Matrix (Fin n) (Fin n) (Fin n) //
      (∀ i, Function.Injective (mat i)) ∧ (∀ j, Function.Injective (mat.transpose j))}
    { toFun     := fun ⟨mat, h⟩ => ⟨mat, h.1, h.2⟩
      invFun    := fun L => ⟨L.mat, L.row_injective, L.col_injective⟩
      left_inv  := fun _ => rfl
      right_inv := fun _ => rfl }

/--
A transversal of a latin square `L` is a selection of one cell per row, given by a
column-selector `σ`, such that the selected columns are all distinct and the symbols at the
selected cells are all distinct.
-/
abbrev IsTransversal (L : LatinSquare n) (σ : Fin n → Fin n) : Prop :=
  Function.Injective σ ∧ Function.Injective (fun i => L.mat i (σ i))

/--
A near-transversal of a latin square `L` of order `n` is a selection of `n - 1` cells,
given by a row-selector `ρ` and a column-selector `σ` (both `Fin (n - 1) → Fin n`),
such that the selected rows are all distinct, the selected columns are all distinct,
and the symbols at the selected cells are all distinct.
-/
abbrev IsNearTransversal (L : LatinSquare n) (ρ σ : Fin (n - 1) → Fin n) : Prop :=
  Function.Injective ρ ∧ Function.Injective σ ∧ Function.Injective (fun i => L.mat (ρ i) (σ i))

/--
The number of transversals of a latin square `L`, defined as the cardinality of the type of
column-selectors `σ : Fin n → Fin n` satisfying `IsTransversal L σ`.
-/
def numTransversals (L : LatinSquare n) : ℕ := Fintype.card {σ : Fin n → Fin n // IsTransversal L σ}
