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

public import FormalConjecturesForMathlib.AlgebraicTopology.OpenRestrictedCohomologyVanishing

/-!
# Canonical lowest-degree section comparison on an ambient open

The coefficient complex stays on the original ambient space. The actual open
restriction, its exact homology comparison, and literal equality of the top open's
image identify the lowest-degree comparison on the restricted space with an
isomorphism between ambient section cohomology and ambient cohomology-sheaf sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- The image of the top open of the subspace is literally its ambient open. -/
theorem openRestrictionTopOpen_eq : U.isOpenEmbedding.functor.obj ⊤ = U := by
  apply SetLike.coe_injective
  change Subtype.val '' Set.univ = (U : Set X)
  simp

/-- Actual global sections of open restriction are ambient sections on the same open. -/
def openRestrictionTopSectionsIso :
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⋙ supportEvaluation (TopCat.of U) ⊤ ≅
      supportEvaluation X U :=
  NatIso.ofComponents (fun F => F.obj.mapIso
    (eqToIso (congrArg op (openRestrictionTopOpen_eq X U))))
    (fun f => (f.hom.naturality _).symm)

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same actual open equality applied to coefficient complexes. -/
def openRestrictionTopSectionComplexIso :
    ((supportEvaluation (TopCat.of U) ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K) ≅
      ((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K :=
  (NatIso.mapHomologicalComplex (openRestrictionTopSectionsIso X U) (.up ℤ)).app K

/-- Exact open restriction identifies sections of the two actual homology sheaves. -/
def openRestrictionHomologyTopSectionsIso (n : ℤ) :
    (((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).obj K).homology n).obj.obj (op (⊤ : Opens (TopCat.of U)))) ≅
        (K.homology n).obj.obj (op U) :=
  (supportEvaluation (TopCat.of U) ⊤).mapIso
    ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})) ≪≫
      (openRestrictionTopSectionsIso X U).app (K.homology n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual lowest-degree comparison on an open where lower cohomology sheaves vanish.
Its maps are fixed by restriction, sheafification, and exact homology functoriality. -/
def openRestrictedLowestSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K).homology j))
    (hflasque : ∀ j, (K.X j).IsFlasque) :
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅
      (K.homology n).obj.obj (op U) := by
  let L := ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℤ)).obj K
  have hLF (j : ℤ) : (L.X j).IsFlasque := by
    let := hflasque j
    exact openSheafRestriction_isFlasque X U (K.X j)
  exact (HomologicalComplex.homologyMapIso (openRestrictionTopSectionComplexIso X U K) n).symm ≪≫
    lowestSectionCohomologyIso (TopCat.of U) L N n hK hLF ⊤ ≪≫
      openRestrictionHomologyTopSectionsIso X U K n

end TopCat.Sheaf
