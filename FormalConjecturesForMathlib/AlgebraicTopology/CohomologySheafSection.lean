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

public import FormalConjecturesForMathlib.AlgebraicTopology.CohomologySheafStalkVanishing

/-!
# Canonical cohomology-sheaf sections from local section-complex classes

Exact sheafification identifies the sheafification of the presheaf of local
section-complex cohomology with the actual cohomology sheaf. Composing its unit
with that identification gives the canonical local-to-sheaf class map. This
provides the target in which normalized local purity classes can be glued.

No exactness of open-set evaluation on sheaves is assumed. The presheaf
homology is taken before sheafification, and the counit is the actual
sheafification counit on the original coefficient complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Sheafification of the local cohomology presheaf is the actual cohomology
sheaf, by exact sheafification and its counit. -/
def sectionCohomologyPresheafSheafificationIso (n : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (sectionCohomologyPresheaf X K n) ≅ K.homology n := by
  let P : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := P.sc n
  let e := NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit)
    (.up ℤ)
  exact (S.mapHomologyIso
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).symm ≪≫
      homologyMapIso (e.app K) n

/-- The canonical map from local cohomology classes to the cohomology sheaf. -/
def sectionCohomologyPresheafToSheaf (n : ℤ) :
    sectionCohomologyPresheaf X K n ⟶ (K.homology n).obj :=
  toSheafify (Opens.grothendieckTopology X) _ ≫
    (sectionCohomologyPresheafSheafificationIso X K n).hom.hom

/-- An actual cohomology class of sections on `U` determines a section of the
actual cohomology sheaf on `U`. -/
def sectionCohomologyToSheafSection (n : ℤ) (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n ⟶
      (K.homology n).obj.obj (op U) :=
  (sectionCohomologyPresheafOnOpenIso X K n U).hom ≫
    (sectionCohomologyPresheafToSheaf X K n).app (op U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical presheaf-to-sheaf class map induces an isomorphism on every
stalk; it does not assert surjectivity of classes on a fixed open set. -/
instance sectionCohomologyPresheafToSheaf_stalk_isIso (n : ℤ) (x : X) :
    IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (sectionCohomologyPresheafToSheaf X K n)) := by
  let := Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (sectionCohomologyPresheaf X K n)
  dsimp only [sectionCohomologyPresheafToSheaf]
  rw [Functor.map_comp]
  infer_instance

end TopCat.Sheaf
