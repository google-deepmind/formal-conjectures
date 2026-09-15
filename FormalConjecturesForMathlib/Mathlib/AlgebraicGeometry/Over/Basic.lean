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

public import Mathlib.AlgebraicGeometry.Scheme

import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Algebra structure on section

When working with schemes over a fixed ring, the section rings of the scheme have a natural
algebra structure that is not currently in Mathlib. We make this an `instance_reducible` def
instead of an instance to avoid a possible diamond with the instance in
`Mathlib.AlgebraicGeometry.Group.Affine`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- The algebra structure on section rings of a scheme over an affine variety. -/
@[instance_reducible]
noncomputable def overSpecAlgebra {R : Type*} [CommRing R] (X : Over (Spec ↧R)) (U : X.left.Opens) :
    Algebra R Γ(X.left, U) :=
  (X.hom.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso ↧R).inv.hom |>.toAlgebra

end AlgebraicGeometry
