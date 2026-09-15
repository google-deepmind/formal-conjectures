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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexSupportedSingularModel
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SupportedSingularSectionCohomology

/-!
# Cohomology-sheaf concentration for smooth closed supports

The complex is the supported-sections kernel applied to the fixed ambient rational injective
resolution. Its open-section homology is compared to relative singular cohomology by the
singular resolution and restriction-cone maps, and cofinal normal neighborhoods then give
stalkwise and sheafwise concentration in degree twice the complex codimension. Identifying
the surviving cohomology sheaf with rational constants on the support is left to a later file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance smoothClosedSupportCohomologySheafAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The literal supported ambient rational injective complex for a closed support. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    (TopCat.of (ComplexPoint X)) S.compl).mapHomologicalComplex (.up ℤ)).obj
      (ambientRationalInjectiveComplex X)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

/-- Actual open-section cohomology of the supported injective model is relative
singular cohomology of the same literal local support pair. -/
def complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint X))
    (V : Opens (ComplexPoint X)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  exact (complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed V n)

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The actual closed analytic image of the smooth closed immersion. -/
def smoothClosedAnalyticSupport : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), (isClosedEmbedding_map_of_closedImmersion i).isClosed_range⟩

end AlgebraicGeometry.ComplexPoint
