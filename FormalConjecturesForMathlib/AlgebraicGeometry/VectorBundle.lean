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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoversTop

universe u v

namespace SheafOfModules

open CategoryTheory Limits

variable {C : Type u} [Category.{v, u} C]
variable {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat} (M : SheafOfModules R)
variable [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrp)]
variable [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrp]
variable [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp]

/-- A vector bundle is a sheaf of modules that is locally isomorphic to
a free sheaf. -/
structure VectorBundleData (M : SheafOfModules.{v} R) where
  /-- The index type for the open cover on which the vector bundle is free. -/
  OpensIndex : Type u
  /-- The indexed family of opens on which the vector bundle is free. -/
  opens : OpensIndex → C
  /-- The indexed family of opens covers the base. -/
  coversTop : J.CoversTop opens
  /-- The indexed family of types that index local bases for the vector bundle. -/
  BasisIndex : OpensIndex → Type v
  /-- The restriction of the vector bundle to one of the opens is free. -/
  locallyFree : ∀ i, (M.over <| opens i) ≅ SheafOfModules.free (BasisIndex i)

structure FiniteRankVectorBundleData (M : SheafOfModules R) extends VectorBundleData M where
  /-- The predicate that every local basis in the defining data of the vector bundle is finite. -/
  finite : ∀ i, Finite (BasisIndex i)

/-- A class for vector bundles of constant finite rank. -/
class IsVectorBundleWithRank (M : SheafOfModules R) (n : ℕ) where
  /-- The predicate that a sheaf of modules is locally free. -/
  exists_vector_bundle_data : ∃ (D : M.FiniteRankVectorBundleData),
    ∀ i, Nat.card (D.BasisIndex i) = n

end SheafOfModules
