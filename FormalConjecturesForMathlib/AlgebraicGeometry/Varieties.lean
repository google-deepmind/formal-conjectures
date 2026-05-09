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

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.Ring.Topology

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/--
An algebraic variety over a field `K` is a reduced scheme of finite type over `Spec K`.
"Of finite type" is encoded as `LocallyOfFiniteType` for the structure morphism together
with `CompactSpace X`. Since `Spec K` is affine, the latter is equivalent to the
structure morphism `X ↘ Spec K` being quasi-compact, so the two conditions together
are equivalent to the morphism being of finite type. -/
class IsAlgebraicVariety (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] : Prop where
  isReduced : IsReduced X
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))

namespace IsAlgebraicVariety

attribute [instance] isReduced
attribute [instance] locallyOfFiniteType

end IsAlgebraicVariety

/-- The set of `K`-rational points of a `K`-scheme `X`, defined as sections of the
structure morphism (equivalently, morphisms `Spec K ⟶ X` over `Spec K`). -/
def RatPoints (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] : Type u :=
  { f : Spec (CommRingCat.of K) ⟶ X // f ≫ X ↘ Spec (CommRingCat.of K) = 𝟙 _ }

/-- The set of `L`-points of a `K`-scheme `X` for a `K`-algebra `L`, defined as
morphisms `Spec L ⟶ X` over `Spec K`. -/
def Points (K L : Type u) [Field K] [CommRing L] [Algebra K L] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] : Type u :=
  { f : Spec (CommRingCat.of L) ⟶ X //
    f ≫ X ↘ Spec (CommRingCat.of K) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) }

/-- Base change of a `K`-rational point to an `L`-point along the algebra map `K → L`. -/
noncomputable def Points.ofRat (K L : Type u) [Field K] [CommRing L] [Algebra K L]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (p : RatPoints K X) : Points K L X :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ p.1, by
    rw [Category.assoc, p.2, Category.comp_id]⟩

namespace Points

variable (K L : Type u) [Field K] [CommRing L] [Algebra K L]
variable [TopologicalSpace L] [IsTopologicalRing L]

open scoped CommRingCat.HomTopology

/-- The natural map sending an `L`-point of `X` to the induced ring hom on global sections,
`Γ(X, ⊤) ⟶ L`. This is the affine functor of points evaluated at `Spec L`. -/
noncomputable def toΓHom {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (p : Points K L X) : Γ(X, ⊤) ⟶ CommRingCat.of L :=
  p.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom

/-- For an open subscheme `U ⊆ X`, the natural map `Points K L U.toScheme → Points K L X`
given by post-composition with the inclusion `U.ι : U.toScheme ⟶ X`. The `K`-structure on
`U.toScheme` is inherited via `U.toScheme.CanonicallyOver X` and `X.Over (Spec K)`. -/
noncomputable def ofOpen {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (U : X.Opens) (p : Points K L U.toScheme) : Points K L X :=
  ⟨p.1 ≫ U.ι, by
    have h : U.toScheme ↘ Spec (CommRingCat.of K) =
        U.ι ≫ X ↘ Spec (CommRingCat.of K) := rfl
    rw [Category.assoc, ← h]
    exact p.2⟩

/-- The real-analytic topology on `Points K L X`.

A subset is open iff for every affine open `U` of `X`, its preimage in
`Points K L U.toScheme` is open with respect to the topology induced by the global-sections
map `p ↦ p^♯ : Points K L U.toScheme → (Γ(U.toScheme, ⊤) ⟶ CommRingCat.of L)`, where the
codomain carries Mathlib's pointwise-convergence topology (see
`CommRingCat.HomTopology`). Equivalently, this is the *final* topology over the family of
inclusions `Points K L U.toScheme ↪ Points K L X` for affine opens `U ⊆ X`.

This is canonical (independent of any choice of cover) because the supremum is taken over
*all* affine opens. -/
noncomputable instance instTopologicalSpace
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] :
    TopologicalSpace (Points K L X) :=
  ⨆ (U : X.affineOpens),
    TopologicalSpace.coinduced (ofOpen K L U.val)
      (TopologicalSpace.induced (toΓHom (K := K) (L := L) (X := U.val.toScheme)) inferInstance)

end Points

end AlgebraicGeometry
