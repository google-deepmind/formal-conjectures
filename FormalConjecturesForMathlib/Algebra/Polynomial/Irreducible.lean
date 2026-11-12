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

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Over a linearly ordered field, `X ^ 2 + a` is irreducible for every `0 < a`, since it has no
root. -/
theorem irreducible_X_sq_add_C_of_pos {a : K} (ha : 0 < a) : Irreducible (X ^ 2 + C a) :=
  irreducible_of_degree_le_three_of_not_isRoot (by simp) fun x hx ↦ by
    simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]

end Polynomial
