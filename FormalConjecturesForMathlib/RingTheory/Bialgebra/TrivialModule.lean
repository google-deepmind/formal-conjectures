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

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public noncomputable section

/-!
# The trivial module of a bialgebra

If `A` is a bialgebra over a commutative ring `R`, the counit `A →ₐ[R] R` makes `R` into an
`A`-module, the trivial module. We package it as the object `Bialgebra.trivialModuleCat R A` of
`ModuleCat A`.
-/

universe u v

namespace Bialgebra

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Bialgebra R A]

/-- The trivial module of the bialgebra `A` over `R`: the ring `R` on which `A` acts through the
counit `A →ₐ[R] R`, as an object of `ModuleCat A`. -/
def trivialModuleCat : ModuleCat.{u} A :=
  letI := Module.compHom R (counitAlgHom R A).toRingHom
  ModuleCat.of A R

variable {R A}

/-- The bialgebra `A` acts on its trivial module through the counit. The carrier of
`trivialModuleCat R A` is `R` by definition, so the product on the right is the product of `R`. -/
lemma trivialModuleCat_smul (a : A) (r : trivialModuleCat R A) :
    a • r = HMul.hMul (α := R) (β := R) (counitAlgHom R A a) r :=
  rfl

end Bialgebra
