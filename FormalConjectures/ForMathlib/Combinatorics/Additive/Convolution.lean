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
import FormalConjectures.ForMathlib.Algebra.Group.Indicator
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Convolution of Functions on ℕ

This file defines the sum (`∗`) convolution of functions `ℕ → R`.

## Main Definitions
* `AdditiveCombinatorics.sumConv`: The sum convolution `f ∗ g`.


## Notation

* `f ∗ g` for `sumConv f g`.
* `𝟙_A` for the indicator function of a set `A`.

## TODO

* `f ∘ g` for `diffConv f g`.
-/


namespace AdditiveCombinatorics

open Finset Classical Set

variable {R : Type*} [Semiring R]

/-- The sum convolution of two functions `f, g : ℕ → R`, also known as the Cauchy product.
`(f ∗ g) n = ∑_{a+b=n} f(a)g(b)`. -/
def sumConv (f g : ℕ → R) (n : ℕ) : R := ∑ p ∈  antidiagonal n, f p.1 * g p.2

infixl:70 " ∗ " => sumConv

/-- The number of sum representations is the sum convolution of `A`'s indicator
function with itself. -/
noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ := (𝟙_A ∗ 𝟙_A) n


@[simp]
lemma sumRep_def (A : Set ℕ) (n : ℕ) :
    sumRep A n = ((antidiagonal n).filter (fun (p : ℕ × ℕ) ↦ p.1 ∈ A ∧ p.2 ∈ A)).card := by
  simp only [sumRep, sumConv, indicatorOne, indicator, mul_ite, mul_one, mul_zero]
  push_cast [← ite_and, card_filter, and_comm]
  congr!

open PowerSeries

theorem sumRep_eq_powerSeries_coeff (A : Set ℕ) (n : ℕ) : (sumRep  A  n : ℕ) =
    ((PowerSeries.mk (𝟙_A)) * (PowerSeries.mk (𝟙_A)) : PowerSeries ℕ).coeff ℕ n := by
  simp [sumRep, sumConv, indicatorOne, indicator, PowerSeries.coeff_mul, PowerSeries.coeff_mk]

end AdditiveCombinatorics
