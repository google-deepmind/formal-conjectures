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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexSheafBorelMoore
public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupportForget

/-!
# From ambient Borel–Moore classes to actual derived ordinary cohomology

The map is the constructed complex-orientation duality followed by the actual
derived support-forgetting map. We prove that forgetting Borel–Moore support first
gives exactly the same result. All targets here use actual derived global sections;
comparison with the repository's separate `H^n(X; ℚ)` presentation remains
a further theorem. In particular, no cycle-component fundamental class is supplied
or constructed by the transport map alone.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

local instance complexSheafForgetAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance complexSheafForgetSheafDerivedCategory : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

local instance complexSheafForgetGroupDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- Ordinary rational sheaf cohomology in the actual derived-global-sections model. -/
def ComplexDerivedCohomology (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X))).obj
      (complexConstantRationalSheafPlusObject X))

/-- The actual derived inclusion of supported cohomology into ordinary cohomology. -/
def complexDerivedSupportedCohomologyForgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    ComplexDerivedSupportedCohomology X Z n ⟶
      ComplexDerivedCohomology X n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
    ((TopCat.Sheaf.derivedForgetClosedSupport
      (TopCat.of (ComplexPoint X)) Z).app
        (complexConstantRationalSheafPlusObject X))

/-- Whole-space support is canonically ordinary cohomology through support forgetting. -/
def complexDerivedSupportedCohomologyTopIso (n : ℤ) :
    ComplexDerivedSupportedCohomology X ⊤ n ≅
      ComplexDerivedCohomology X n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).mapIso
    ((TopCat.Sheaf.derivedClosedSupportSectionsTopIso
      (TopCat.of (ComplexPoint X))).app
        (complexConstantRationalSheafPlusObject X))

@[simp]
theorem complexDerivedSupportedCohomologyTopIso_hom (n : ℤ) :
    (complexDerivedSupportedCohomologyTopIso X n).hom =
      complexDerivedSupportedCohomologyForgetSupport X ⊤ n := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Support enlargement and forgetting support induce the same ordinary class. -/
@[reassoc (attr := simp)]
theorem complexDerivedSupportedCohomologySupportMap_forget
    {Z W : Closeds (ComplexPoint X)} (h : Z ≤ W) (n : ℤ) :
    complexDerivedSupportedCohomologySupportMap X h n ≫
        complexDerivedSupportedCohomologyForgetSupport X W n =
      complexDerivedSupportedCohomologyForgetSupport X Z n := by
  unfold complexDerivedSupportedCohomologySupportMap complexDerivedSupportedCohomologyForgetSupport
  rw [← Functor.map_comp]
  congr 1
  exact NatTrans.congr_app (TopCat.Sheaf.derivedClosedSupportSectionsMap_forget
    (TopCat.of (ComplexPoint X)) h) _

variable [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]

/-- Transport an actual ambient Borel–Moore class to ordinary derived cohomology,
using the constructed complex orientation and the actual support inclusion. -/
def complexAmbientSheafBorelMooreToCohomology
    (Z : Closeds (ComplexPoint X)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology X d Z i ⟶
      ComplexDerivedCohomology X (2 * (d : ℤ) - i) :=
  (complexAmbientSheafBorelMooreHomologyIso X d Z i).hom ≫
    complexDerivedSupportedCohomologyForgetSupport X Z (2 * (d : ℤ) - i)

/-- Enlarging Borel–Moore support does not change the resulting ordinary cohomology class. -/
@[reassoc (attr := simp)]
theorem complexAmbientSheafBorelMooreToCohomology_naturality
    {Z W : Closeds (ComplexPoint X)} (h : Z ≤ W) (i : ℤ) :
    complexAmbientSheafBorelMooreSupportMap X d h i ≫
        complexAmbientSheafBorelMooreToCohomology X d W i =
      complexAmbientSheafBorelMooreToCohomology X d Z i := by
  unfold complexAmbientSheafBorelMooreToCohomology
  rw [complexAmbientSheafBorelMooreHomologyIso_naturality_assoc,
    complexDerivedSupportedCohomologySupportMap_forget]

/-- Forgetting Borel–Moore support first, then applying whole-space duality, is exactly
the supported-duality construction. No independent whole-space comparison is chosen. -/
theorem complexAmbientSheafBorelMooreToCohomology_eq_forgetSupport
    (Z : Closeds (ComplexPoint X)) (i : ℤ) :
    complexAmbientSheafBorelMooreToCohomology X d Z i =
      complexAmbientSheafBorelMooreForgetSupport X d Z i ≫
        (complexAmbientSheafBorelMooreHomologyIso X d ⊤ i).hom ≫
        (complexDerivedSupportedCohomologyTopIso X (2 * (d : ℤ) - i)).hom :=
  (complexAmbientSheafBorelMooreToCohomology_naturality X d le_top i).symm

/-- The cycle-degree transport, with the dimension arithmetic already proved in duality. -/
def complexAmbientSheafBorelMooreCycleDegreeToCohomology
    (Z : Closeds (ComplexPoint X)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology X d Z
        (2 * ((d - p : ℕ) : ℤ)) ⟶
      ComplexDerivedCohomology X (2 * (p : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeIso X d Z p hp).hom ≫
    complexDerivedSupportedCohomologyForgetSupport X Z (2 * (p : ℤ))

end AlgebraicGeometry.ComplexPoint
