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

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.Ext.GradedAlgebra
public import FormalConjecturesForMathlib.RingTheory.Bialgebra.TrivialModule

@[expose] public noncomputable section

/-!
# Cohomology of a bialgebra

Let `A` be a bialgebra over a field `k`, and let `k` be the trivial `A`-module through the counit
(`Bialgebra.trivialModuleCat k A`). We define

* `Bialgebra.cohomologyRing k A`: the cohomology ring `H^*(A, k) = ⨁ n, Ext^n_A(k, k)`, a graded
  `k`-algebra under the Yoneda product;
* `Bialgebra.cohomology k A M`: the cohomology `H^*(A, M) = ⨁ n, Ext^n_A(k, M)` with coefficients
  in an `A`-module `M`, a graded module over `H^*(A, k)`.

Here `Ext` is taken in `ModuleCat A`, the category of all `A`-modules, and not in the category of
finite-dimensional ones. When `A` is finite-dimensional over a field the two give the same groups
on finite-dimensional modules: such a module admits a resolution by finitely generated free
`A`-modules, which are again finite-dimensional and are projective in both categories, and `Ext`
is computed from that single resolution either way. So `cohomologyRing k A` is the cohomology of
the finite tensor category of finite-dimensional `A`-modules, which is what the literature means
by `H^*(A, k)`.

Two `k`-structures on `ModuleCat A` are involved, and only one of them is scoped.
`ModuleCat.linearOverField`, giving `Linear k (ModuleCat A)`, is a global instance, so the
`k`-algebra structure on `cohomologyRing k A` registered below needs no `open scoped`. The
`k`-module structure on an individual object, `ModuleCat.moduleOfAlgebraModule`, is a *scoped*
instance; in both, `k` acts through `algebraMap k A`. A file that mentions `FiniteDimensional k M`
for `M : ModuleCat A` therefore does have to `open scoped ModuleCat.Algebra`.
-/

open CategoryTheory Abelian
open scoped DirectSum ModuleCat.Algebra

universe u

namespace Bialgebra

variable (k : Type u) [Field k] (A : Type u) [Ring A] [Bialgebra k A]

/-- The cohomology ring `H^*(A, k) = ⨁ n, Ext^n_A(k, k)` of the bialgebra `A` over `k`, where `k`
is the trivial `A`-module through the counit and `Ext` is taken in `ModuleCat A`. It is a graded
`k`-algebra under the Yoneda product. -/
abbrev cohomologyRing : Type u :=
  ⨁ n, Ext (trivialModuleCat k A) (trivialModuleCat k A) n

/-- The cohomology `H^*(A, M) = ⨁ n, Ext^n_A(k, M)` of the bialgebra `A` over `k` with
coefficients in the `A`-module `M`. It is a graded module over `cohomologyRing k A` under the
Yoneda product. -/
abbrev cohomology (M : ModuleCat.{u} A) : Type u :=
  ⨁ n, Ext (trivialModuleCat k A) M n

instance : Algebra k (cohomologyRing k A) :=
  inferInstance

instance (M : ModuleCat.{u} A) : Module (cohomologyRing k A) (cohomology k A M) :=
  inferInstance

variable {k A}

/-- The product on `cohomologyRing k A` is the Yoneda composition of extensions. -/
lemma cohomologyRing_of_mul_of {a b : ℕ}
    (x : Ext (trivialModuleCat k A) (trivialModuleCat k A) a)
    (y : Ext (trivialModuleCat k A) (trivialModuleCat k A) b) :
    (DirectSum.of _ a x : cohomologyRing k A) * DirectSum.of _ b y =
      DirectSum.of _ (a + b) (x.comp y rfl) :=
  DirectSum.of_mul_of x y

variable (k A) in
/-- A scalar `c : k` acts on `cohomologyRing k A` as `c` times the identity in degree `0`. -/
lemma cohomologyRing_algebraMap_apply (c : k) :
    algebraMap k (cohomologyRing k A) c =
      DirectSum.of _ 0 (Ext.mk₀ (c • 𝟙 (trivialModuleCat k A))) :=
  rfl

/-- The cohomology ring is not the zero ring: its degree-zero part contains the identity of the
trivial module. In particular a finiteness statement about `cohomologyRing k A` is not vacuous. -/
lemma nontrivial_cohomologyRing : Nontrivial (cohomologyRing k A) := by
  have hid : (𝟙 (trivialModuleCat k A)) ≠ 0 := by
    intro h
    have h1 : (1 : k) = 0 := congrArg (fun f => ModuleCat.Hom.hom f (1 : k)) h
    exact one_ne_zero h1
  have hmk : (Ext.mk₀ (𝟙 (trivialModuleCat k A)) : Ext _ _ 0) ≠ 0 := fun h =>
    hid ((Ext.mk₀_bijective (trivialModuleCat k A) (trivialModuleCat k A)).injective
      (by simpa using h))
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  apply hmk
  rw [DirectSum.one_def] at h
  rw [← Ext.gOne_eq]
  exact DirectSum.of_injective
    (β := fun n ↦ Ext (trivialModuleCat k A) (trivialModuleCat k A) n) 0 (by simpa using h)

/-- The action of `cohomologyRing k A` on `cohomology k A M` is the Yoneda composition of
extensions. -/
lemma cohomology_of_smul_of {M : ModuleCat.{u} A} {a b : ℕ}
    (x : Ext (trivialModuleCat k A) (trivialModuleCat k A) a)
    (y : Ext (trivialModuleCat k A) M b) :
    (DirectSum.of _ a x : cohomologyRing k A) • (DirectSum.of _ b y : cohomology k A M) =
      DirectSum.of _ (a + b) (x.comp y rfl) :=
  DirectSum.Gmodule.of_smul_of (A := fun n ↦ Ext (trivialModuleCat k A) (trivialModuleCat k A) n)
    (M := fun n ↦ Ext (trivialModuleCat k A) M n) x y

end Bialgebra
