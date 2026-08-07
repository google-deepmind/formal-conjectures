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

public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic.FieldSimp

public section

namespace QuadraticAlgebra

variable {K : Type*} [Field K] {a b : K} [Fact (∀ r, r ^ 2 ≠ a + b * r)]

attribute [-instance] instField

@[simps] instance : NNRatCast (QuadraticAlgebra K a b) where nnratCast q := ⟨q, 0⟩
@[simps] instance : RatCast (QuadraticAlgebra K a b) where ratCast q := ⟨q, 0⟩

-- TODO: Replace in mathlib. See https://github.com/leanprover-community/mathlib4/pull/38818
/-- If `K` is a field and there is no `r : K` such that `r ^ 2 = a + b * r`,
then `QuadraticAlgebra K a b` is a field. -/
instance instField' : Field (QuadraticAlgebra K a b) where
  inv z := (norm z)⁻¹ • star z
  mul_inv_cancel z hz := by
    rw [ne_eq, ← norm_eq_zero_iff_eq_zero] at hz
    simp only [Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul, C_eq_algebraMap, ← algebraMap_norm_eq_mul_star, ← map_mul,
      inv_mul_cancel₀ hz, map_one]
  inv_zero := by simp
  nnratCast_def q :=
    show _ = _ * (norm (_ : QuadraticAlgebra K a b))⁻¹ • star (_ : QuadraticAlgebra K a b) by
      ext <;> simp [sq]; field_simp; simp [NNRat.cast_def]
  ratCast_def q :=
    show _ = _ * (norm (_ : QuadraticAlgebra K a b))⁻¹ • star (_ : QuadraticAlgebra K a b) by
      ext <;> simp [sq]; field_simp; simp [Rat.cast_def]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext <;> simp [NNRat.smul_def]
  qsmul_def q x := by ext <;> simp [Rat.smul_def]

end QuadraticAlgebra
