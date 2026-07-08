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

import FormalConjecturesForMathlib.Combinatorics.Additive.GowersNorm

open Complex

variable {G : Type*} [AddCommGroup G]

/-- The multiplicative derivative with step 0 evaluates to the function multiplied by its conjugate. -/
lemma multiplicativeDerivative_zero (f : G → ℂ) (x : G) :
    multiplicativeDerivative 0 f x = f x * star (f x) := by
  simp [multiplicativeDerivative]

/-- The multiplicative derivative of a constant function is constant. -/
lemma multiplicativeDerivative_const (h : G) (c : ℂ) (x : G) :
    multiplicativeDerivative h (fun _ ↦ c) x = c * star c := by
  rfl

/-- The multiplicative derivative is invariant under translation of the input function. -/
lemma multiplicativeDerivative_add_right (h : G) (f : G → ℂ) (x y : G) :
    multiplicativeDerivative h (fun z ↦ f (z + y)) x = multiplicativeDerivative h f (x + y) := by
  simp [multiplicativeDerivative, add_right_comm]

/-- The multiplicative derivative distributes over the product of two functions. -/
lemma multiplicativeDerivative_mul (h : G) (f g : G → ℂ) :
    multiplicativeDerivative h (f * g) = multiplicativeDerivative h f * multiplicativeDerivative h g := by
  ext x
  simp only [multiplicativeDerivative, Pi.mul_apply, star_mul]
  ring

/-- The multiplicative derivative of a conjugated function. -/
lemma multiplicativeDerivative_star (h : G) (f : G → ℂ) (x : G) :
    multiplicativeDerivative h (star f) x = star (f x) * f (x + h) := by
  simp [multiplicativeDerivative]

/-- Taking the derivative with a negative step is equivalent to conjugating and shifting the positive derivative. -/
lemma multiplicativeDerivative_neg_add (h : G) (f : G → ℂ) (x : G) :
    multiplicativeDerivative (-h) f (x + h) = star (multiplicativeDerivative h f x) := by
  simp [multiplicativeDerivative, add_assoc, add_neg_cancel]
  ring

/-- Iterated multiplicative derivatives commute. -/
lemma multiplicativeDerivative_comm (h1 h2 : G) (f : G → ℂ) :
    multiplicativeDerivative h1 (multiplicativeDerivative h2 f) =
    multiplicativeDerivative h2 (multiplicativeDerivative h1 f) := by
  ext x
  simp [multiplicativeDerivative, add_right_comm]
  ring
