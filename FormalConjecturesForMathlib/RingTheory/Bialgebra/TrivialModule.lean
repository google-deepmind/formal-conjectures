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

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public noncomputable section

/-!
# The trivial module of a bialgebra

If `A` is a bialgebra over a commutative ring `R`, the counit `A →ₐ[R] R` makes `R` into an
`A`-module, the trivial module. We package it as the object `Bialgebra.trivialModuleCat R A` of
`ModuleCat A`.

Over a field `k`, restricting scalars along `algebraMap k A` recovers the `k`-module structure of
`k` itself (`Bialgebra.trivialModuleCat_smul_base`), so the trivial module is one-dimensional;
`Bialgebra.trivialModuleCatLinearEquiv` and the `FiniteDimensional` instance record this. That
`k`-module structure is `ModuleCat.moduleOfAlgebraModule`, a *scoped* instance, so a file stating
`FiniteDimensional k (trivialModuleCat k A)` must `open scoped ModuleCat.Algebra`.
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

section Field

open scoped ModuleCat.Algebra

variable {k : Type u} {B : Type v} [Field k] [Ring B] [Bialgebra k B]

/-- The `k`-module structure on the trivial module of a bialgebra over a field `k`, obtained by
restricting scalars along `algebraMap k B`, is the module structure of `k` itself: the counit is a
`k`-algebra map, so it sends `algebraMap k B c` to `c`. -/
lemma trivialModuleCat_smul_base (c : k) (r : trivialModuleCat k B) :
    c • r = HMul.hMul (α := k) (β := k) c r := by
  rw [show c • r = (algebraMap k B c) • r from rfl, trivialModuleCat_smul,
    AlgHom.commutes]
  rfl

variable (k B) in
/-- The trivial module of a bialgebra over a field `k` is `k` itself as a `k`-module; in
particular it is one-dimensional. -/
def trivialModuleCatLinearEquiv : trivialModuleCat k B ≃ₗ[k] k where
  toFun r := r
  map_add' _ _ := rfl
  map_smul' := trivialModuleCat_smul_base
  invFun r := r
  left_inv _ := rfl
  right_inv _ := rfl

instance : FiniteDimensional k (trivialModuleCat k B) :=
  Module.Finite.equiv (trivialModuleCatLinearEquiv k B).symm

end Field

end Bialgebra
