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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.HomologySheafSection
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.DerivedSheafSupportLocalization
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueQuasiIsoGlobalSections
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology-sheaf stalk vanishing from cofinal local section calculations

For a complex of additive sheaves, the stalk of the homology presheaf of its
underlying presheaf complex is canonically the stalk of its homology sheaf.
Both comparisons use exact stalk functors; evaluation on an open set is not
mistakenly treated as exact on sheaves.

Consequently, vanishing of section-complex homology on a cofinal system of
neighborhoods implies vanishing of the cohomology-sheaf stalk. The neighborhood
may depend on the original open set; no single neighborhood is silently
substituted for a cofinal family. This is the generic passage from the local
normal-slice calculation to sheaf support purity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

end TopCat.Presheaf

namespace TopCat.Sheaf

open AlgebraicTopology.Singular

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The presheaf homology of the actual underlying complex. This is not defined
as evaluation of the cohomology sheaf, since that evaluation is not exact. -/
def sectionCohomologyPresheaf (n : ℤ) : Presheaf AddCommGrpCat.{u} X :=
  (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).homology n

/-- Exact evaluation of presheaves identifies section-complex homology with
the homology presheaf on the same open set. -/
def sectionCohomologyPresheafOnOpenIso (n : ℤ) (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅
      (sectionCohomologyPresheaf X K n).obj (op U) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    ((((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n)
  exact S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

/-- The homology presheaf and actual homology sheaf have canonically equal stalks.
The underlying sheaf-forgetful functor is not assumed exact. -/
def sectionCohomologyPresheafStalkIso (n : ℤ) (x : X) :
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (sectionCohomologyPresheaf X K n) ≅
      (additiveSheafStalkFunctor X x).obj (K.homology n) := by
  let S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    K.sc n
  let P : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n
  exact (P.mapHomologyIso (additivePresheafStalkFunctor X x)).symm ≪≫
    S.mapHomologyIso (additiveSheafStalkFunctor X x)

end TopCat.Sheaf
