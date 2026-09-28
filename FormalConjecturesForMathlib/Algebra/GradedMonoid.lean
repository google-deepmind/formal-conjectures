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

public import Mathlib.Algebra.GradedMonoid

@[expose] public section

/-!
# Equality in a graded monoid

`GradedMonoid.mk_eq_mk` proves an equality `GradedMonoid.mk i a = GradedMonoid.mk j b` from
`i = j` and `HEq a b`. It is `Sigma.ext` stated for `GradedMonoid.mk`, so that unification only
sees the arguments of `GradedMonoid.mk` and never has to reduce projections of the two sides.
-/

namespace GradedMonoid

variable {ι : Type*} {A : ι → Type*}

/-- Equality of two elements of `GradedMonoid A` written with `GradedMonoid.mk`. -/
lemma mk_eq_mk {i j : ι} {a : A i} {b : A j} (h : i = j) (h' : HEq a b) :
    GradedMonoid.mk i a = GradedMonoid.mk j b :=
  Sigma.ext h h'

end GradedMonoid
