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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SupportedSectionRestrictionCone

/-!
# Actual supported-section kernels and open restriction cones

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SupportedSectionRestrictionCone`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

variable (U V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- On an open contained in the excluded open, the actual supported-section group is
zero because its defining restriction map is an isomorphism. -/
theorem supportedOutsideSections_isZero_of_le (F : Sheaf AddCommGrpCat.{u} X)
    (hVU : V ≤ U) :
    IsZero (((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V)) := by
  have he : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hVU]
  have hi : IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V) := by
    rw [show U.isOpenEmbedding.isOpenMap.adjunction.counit.app V = eqToHom he from
      Subsingleton.elim _ _]
    infer_instance
  let r := ((toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have : IsIso r := by
    change IsIso (F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op)
    infer_instance
  exact (isZero_kernel_of_mono r).of_iso (sheafSectionsSupportedOutsideOnOpenIso X U V F)

end TopCat.Sheaf
