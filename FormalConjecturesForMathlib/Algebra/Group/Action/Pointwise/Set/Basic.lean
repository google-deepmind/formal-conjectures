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
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

open scoped Pointwise

namespace Set
variable {M : Type*} [Monoid M] {a b : M} {s : Set M}

@[to_additive (attr := simp)]
lemma mul_mem_smul_set [IsLeftCancelMul M] : a * b ∈ a • s ↔ b ∈ s :=
  (mul_right_injective _).mem_set_image

end Set
