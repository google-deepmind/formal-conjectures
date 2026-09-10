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

public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupport
public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShift

/-!
# Coherent shifts of concrete derived sections with support

Both concrete bounded-below support functors commute coherently with every
integer shift. This is constructed from their injective-resolution derived
units, via the generic `rightDerivedFunctorPlusCommShift` theorem. There is no
shift-comparison input. The localization/cone comparison and membership of a
proposed dualizing complex in the bounded-below category remain separate tasks.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

local instance : HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

/-- Sheaf-valued derived sections with support commute coherently with shifts. -/
instance derivedSheafSectionsWithClosedSupport_commShift (Z : Closeds X) :
    (derivedSheafSectionsWithClosedSupport X Z).CommShift ℤ := by
  dsimp only [derivedSheafSectionsWithClosedSupport]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-valued derived unit respects the constructed shifts. -/
instance derivedSheafSectionsWithClosedSupportUnit_commShift (Z : Closeds X) :
    NatTrans.CommShift (derivedSheafSectionsWithClosedSupportUnit X Z) ℤ :=
  Functor.rightDerivedFunctorPlusUnitCommShift (sheafSectionsWithClosedSupport X Z)

/-- The canonical natural isomorphism `RΓ̲_Z(K[n]) ≅ (RΓ̲_Z K)[n]`. -/
def derivedSheafSectionsWithClosedSupportShiftIso (Z : Closeds X) (n : ℤ) :
    shiftFunctor (DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X)) n ⋙
        derivedSheafSectionsWithClosedSupport X Z ≅
      derivedSheafSectionsWithClosedSupport X Z ⋙
        shiftFunctor (DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X)) n :=
  (derivedSheafSectionsWithClosedSupport X Z).commShiftIso n

/-- Group-valued derived sections with support commute coherently with shifts. -/
instance derivedClosedSupportSections_commShift (Z : Closeds X) :
    (derivedClosedSupportSections X Z).CommShift ℤ := by
  dsimp only [derivedClosedSupportSections]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The group-valued derived unit respects the constructed shifts. -/
instance derivedClosedSupportSectionsUnit_commShift (Z : Closeds X) :
    NatTrans.CommShift (derivedClosedSupportSectionsUnit X Z) ℤ :=
  Functor.rightDerivedFunctorPlusUnitCommShift (closedSupportSections X Z)

/-- The canonical natural isomorphism `RΓ_Z(K[n]) ≅ (RΓ_Z K)[n]`. -/
def derivedClosedSupportSectionsShiftIso (Z : Closeds X) (n : ℤ) :
    shiftFunctor (DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X)) n ⋙
        derivedClosedSupportSections X Z ≅
      derivedClosedSupportSections X Z ⋙
        shiftFunctor (DerivedCategory.Plus AddCommGrpCat.{u}) n :=
  (derivedClosedSupportSections X Z).commShiftIso n

end TopCat.Sheaf
