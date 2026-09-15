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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.DerivedSheafSupport

/-!
# Concrete sheaf sections with support and their right derived functor

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.DerivedSheafSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Uniqueness in the universal property of supported sections. -/
lemma liftSheafSectionsSupportedOutside_unique (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0)
    (g : F ⟶ (sheafSectionsSupportedOutside X U).obj G)
    (hg : g ≫ (sheafSectionsSupportedOutsideInclusion X U).app G = f) :
    g = liftSheafSectionsSupportedOutside X U f hf :=
  (cancel_mono (kernel.ι _)).1 (hg.trans (kernel.lift_ι _ _ _).symm)

attribute [local instance] supportSheafHasDerivedCategory

attribute [local instance] supportGroupsHasDerivedCategory

end TopCat.Sheaf
