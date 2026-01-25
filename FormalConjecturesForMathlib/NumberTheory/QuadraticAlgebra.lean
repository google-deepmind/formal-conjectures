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
import Mathlib
import FormalConjecturesForMathlib.Algebra.QuadraticAlgebra.Defs

open Module NumberField

namespace QuadraticAlgebra
variable {d : ℕ}

lemma discr_rat_of_modEq_one (hd₁ : d ≠ 1) (hd : Squarefree d) (hd₄ : d ≡ 1 [ZMOD 4]) :
    discr (QuadraticAlgebra ℚ d 0) = d := sorry

lemma discr_rat_of_not_modEq_one (hd : Squarefree d) (hd₄ : ¬ d ≡ 1 [ZMOD 4]) :
    discr (QuadraticAlgebra ℚ d 0) = 4 * d := sorry

end QuadraticAlgebra

/-- Fundamental discriminants are those integers `D` that appear as discriminants of quadratic
fields.

`D` is a fundamental discriminant if it is either of the form `4m` for `m` congruent to `2` or `3`
mod `4` squarefree, or if it congruent to `1` mod `4` and squarefree. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  4 ∣ D ∧ (D / 4 ≡ 2 [ZMOD 4] ∨ D / 4 ≡ 3 [ZMOD 4]) ∧ Squarefree (D / 4) ∨
    D ≡ 1 [ZMOD 4] ∧ Squarefree D

lemma isFundamentalDiscr_iff_exists_discr_eq {D : ℤ} :
    IsFundamentalDiscr D ↔ ∃ d ≠ 1, Squarefree d ∧ discr ℚ (QuadraticAlgebra ℚ d 0) = d := by
  constructor
  · rintro (⟨\d, rfl⟩)
