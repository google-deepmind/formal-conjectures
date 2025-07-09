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

universe u v u' v'

namespace SheafOfModules

open CategoryTheory Limits

variable {C : Type u} [CategoryTheory.Category.{v, u} C]
variable {J : CategoryTheory.GrothendieckTopology C}
variable {R : CategoryTheory.Sheaf J RingCat} (M : SheafOfModules R)
variable [∀ (X : C), (J.over X).HasSheafCompose (CategoryTheory.forget₂ RingCat AddCommGrp)]
variable [∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrp]
variable [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp]

/-- A vector bundle is a sheaf of modules that is locally isomorphic to
a free sheaf. -/
structure VectorBundleData (M : SheafOfModules R) where
  I : Type u
  X : I → C
  --TODO(lezeau) : we probably need to be more careful with
  --universes here.
  I' : I → Type _
  coversTop : J.CoversTop X
  locallyFree : ∀ i, (M.over <| X i) ≅ SheafOfModules.free (I' i)

structure FiniteRankVectorBundleData (M : SheafOfModules R) extends VectorBundleData M where
  finite : ∀ i, Finite (I' i)

/-- A class for vector bundles of constant finite rank. -/
class IsVectorBundleWithRank (M : SheafOfModules R) (n : ℕ) where
  exists_vector_bundle_data : ∃ (D : M.FiniteRankVectorBundleData),
    ∀ i, Nat.card (D.I' i) = n

end SheafOfModules
