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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportPurity

/-!
# Actual purity along the smooth locus of an integral cycle component

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportPurity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

attribute [local instance] cycleComponentSmoothSupportPurityAnalyticTopology

/-- Restricting the actual flasque supported coefficient sheaves preserves flasqueness. -/
theorem cycleComponentSmoothRestrictedInjectiveComplex_isFlasque (n : ℤ) :
    ((cycleComponentSmoothRestrictedInjectiveComplex X x).X n).IsFlasque := by
  let : ((complexSupportInjectiveComplex X
      (cycleComponentAnalyticClosedSupport X x)).X n).IsFlasque :=
    TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X n)
  exact TopCat.Sheaf.openSheafRestriction_isFlasque
    (TopCat.of (ComplexPoint X)) (cycleComponentSmoothSupportAmbientOpen X x)
      ((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).X n)

include d hx in
/-- The actual lower cohomological bound along the smooth locus. -/
theorem cycleComponentSmoothRestrictedInjective_isGE :
    (cycleComponentSmoothRestrictedInjectiveComplex X x).IsGE (2 * (p : ℤ)) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    X x (d := d) hx n (ne_of_lt hn)

include d hx in
/-- The actual upper cohomological bound, hence concentration rather than just lower purity. -/
theorem cycleComponentSmoothRestrictedInjective_isLE :
    (cycleComponentSmoothRestrictedInjectiveComplex X x).IsLE (2 * (p : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    X x (d := d) hx n (ne_of_gt hn)

/-- Its forward map displays the actual open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem cycleComponentSmoothSupportLowestSectionCohomologyIso_hom :
    (cycleComponentSmoothSupportLowestSectionCohomologyIso X x (d := d) hx).hom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint X))
          (cycleComponentSmoothSupportAmbientOpen X x)
          (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).inv
        (2 * (p : ℤ)) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))
        (cycleComponentSmoothRestrictedInjectiveComplex X x) (2 * (p : ℤ)) ⊤ ≫
      (TopCat.Sheaf.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ))).hom := rfl

include d hx in
/-- Actual supported section cohomology on the boundary complement vanishes below `2p`.
Higher-degree global vanishing is not inferred from sheaf concentration. -/
theorem cycleComponentSmoothSupportSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * (p : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · intro j
    exact TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j)
  · intro j hj y hy V hyV
    exact cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
      X x (d := d) hx j (ne_of_lt (hj.trans_lt hn)) y hy V hyV

end AlgebraicGeometry.ComplexPoint
