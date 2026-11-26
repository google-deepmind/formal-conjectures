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

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Algebra.Pi
/-!
# Analysis of Boolean Functions: Basic Definitions

Author: Alexey Milovanov

This module provides the foundational definitions for the analysis of Boolean functions,
following the conventions of Ryan O'Donnell's book "Analysis of Boolean Functions".
It includes the definition of the Hamming cube, Fourier expansion basics, and
linear threshold functions (LTFs).
-/

@[expose] public section

open Finset BigOperators

namespace BooleanAnalysis

variable {n : ℕ}

/-! ### Basic types and algebraic structure -/

/-- The Hamming cube `{0, 1}^n`, represented as functions from `Fin n` to `ZMod 2`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- A real-valued Boolean function on the Hamming cube. -/
def BooleanFunction (n : ℕ) := Cube n → ℝ

instance : CommRing (BooleanFunction n) := inferInstanceAs (CommRing (Cube n → ℝ))
instance : Algebra ℝ (BooleanFunction n) := inferInstanceAs (Algebra ℝ (Cube n → ℝ))

instance : FunLike (BooleanFunction n) (Cube n) ℝ where
  coe f := f
  coe_injective' _ _ h := h

/-! ### Encoding and parity functions -/

/-- A Boolean function is considered Boolean-valued if its range is `{-1, 1}`. -/
def IsBooleanValued (f : BooleanFunction n) : Prop := ∀ x, f x = 1 ∨ f x = -1

/-- The standard character encoding mapping `0 ↦ 1` and `1 ↦ -1`. -/
def chi : ZMod 2 → ℝ := fun b => if b = 0 then 1 else -1

/-- The parity function `χ_S(x) = ∏_{i ∈ S} χ(x_i)`. -/
noncomputable def parityFun (S : Finset (Fin n)) : BooleanFunction n :=
  fun x => ∏ i ∈ S, chi (x i)

scoped prefix:max "χ" => parityFun

/-! ### Expectation -/

/-- The uniform expectation of a Boolean function over the Hamming cube. -/
noncomputable def expect (f : BooleanFunction n) : ℝ := Finset.univ.expect f

scoped notation "𝔼[" f "]" => expect f

/-- A Boolean function is unbiased if its expected value is exactly zero. -/
def IsUnbiased (f : BooleanFunction n) : Prop := 𝔼[f] = 0

/-! ### Fourier coefficients and weights -/

/-- The Fourier coefficient of `f` on the set `S`, defined directly as `𝔼[f · χ_S]`. -/
noncomputable def fourierCoeff (f : BooleanFunction n) (S : Finset (Fin n)) : ℝ :=
  𝔼[fun x => f x * (χ S) x]

scoped notation "𝓕" => fourierCoeff

/-- The Fourier weight of `f` on the set `S`, defined as the squared Fourier coefficient. -/
noncomputable def fourierWeight (f : BooleanFunction n) (S : Finset (Fin n)) : ℝ :=
  𝓕 f S ^ 2

/-- The cumulative Fourier weight of `f` up to degree `k`, denoted as `W^{≤k}[f]`. -/
noncomputable def fourierWeightUpToDegree (f : BooleanFunction n) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k), fourierWeight f S

scoped notation "𝐖_≤" => fourierWeightUpToDegree

/-! ### Linear threshold functions -/

/-- A function is a Linear Threshold Function (LTF) if it can be represented
as the sign of a degree-1 polynomial over the reals. -/
def IsLTF (f : BooleanFunction n) : Prop :=
  ∃ (w : Fin n → ℝ) (θ : ℝ), ∀ x : Cube n,
    f x = if (∑ i, w i * chi (x i)) ≥ θ then 1 else -1

end BooleanAnalysis
