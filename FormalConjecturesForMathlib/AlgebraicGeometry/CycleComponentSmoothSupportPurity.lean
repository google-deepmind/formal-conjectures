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

public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentSmoothClosedLift
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportOpenTransport
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import FormalConjecturesForMathlib.AlgebraicTopology.OpenRestrictedLowestCohomology
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Actual purity along the smooth locus of an integral cycle component

The coefficient complex is the original ambient injective resolution, with support in
the full cycle component, restricted to the complement of the canonical singular
boundary. Actual normal neighborhoods of the smooth-locus closed lift prove that its
cohomology sheaves are concentrated in degree `2p`. No projectivity of the open ambient,
local purity data, or comparison equivalence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

local instance cycleComponentSmoothSupportPurityAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The exact analytic complement of the canonical singular boundary. -/
abbrev cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  (cycleComponentSingularAnalyticClosedFiltration X x 0).compl

include d hx in
/-- Actual cofinal ambient relative-cohomology calculations along the smooth locus. -/
theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X) (hy : y ∈ cycleComponentSupport X x)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentSupport X x)) n)) := by
  let O := cycleComponentSmoothLocusAmbientOpen X x
  let OX := cycleComponentSmoothLocusAmbientOpenOver X x
  let Y := cycleComponentSmoothLocusOver X x
  let i : Y ⟶ OX := cycleComponentSmoothLocusClosedLiftOver X x
  let : SmoothOfRelativeDimension (d - p) Y.hom :=
    cycleComponentSmoothLocus_smoothOfRelativeDimension X x (d := d) hx
  have : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d O.ι X.hom
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹' cycleComponentSupport X x = Set.range (Point.map i) :=
    (cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm
  obtain ⟨w, rfl⟩ := (cycleComponentSmoothLocusAmbientOpen_analytic_image X x).ge hyU
  obtain ⟨z, rfl⟩ := hS.le hy
  have hpd : p ≤ d := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := d) x
    rw [hx] at h
    exact_mod_cast h
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    OX Y i (d - p) d f (isOpenEmbedding_map_open X O)
    (cycleComponentSupport X x) hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include d hx in
/-- Cofinal supported-section vanishing for the literal original ambient resolution. -/
theorem cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X) (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex X
          (cycleComponentAnalyticClosedSupport X x))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ cycleComponentSupport X x
    · obtain ⟨W, hWV, hyW, hW⟩ :=
        cycleComponentSmoothSupport_exists_relativeCohomology_vanishing X x (d := d) hx
          y hy hyU V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentAnalyticClosedSupport X x).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

/-- Restriction of the original full-support injective model to the boundary complement. -/
def cycleComponentSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))) ℤ := by
  let U : Opens (TopCat.of (ComplexPoint X)) := cycleComponentSmoothSupportAmbientOpen X x
  exact ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance cycleComponentSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (cycleComponentSmoothRestrictedInjectiveComplex X x).IsStrictlyGE 0 := by
  dsimp [cycleComponentSmoothRestrictedInjectiveComplex]
  infer_instance

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
/-- The actual restricted cohomology sheaves are concentrated in degree `2p`. -/
theorem cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    IsZero ((cycleComponentSmoothRestrictedInjectiveComplex X x).homology n) :=
  TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X)) _ _ n
    (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x (d := d) hx n hn)

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

/-- The canonical lowest-degree isomorphism using the original ambient resolution and
the original ambient cohomology sheaf, both evaluated on the boundary complement. -/
def cycleComponentSmoothSupportLowestSectionCohomologyIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) ≅
      ((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).homology
        (2 * (p : ℤ))).obj.obj (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (ComplexPoint X)) (cycleComponentSmoothSupportAmbientOpen X x)
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    0 (2 * (p : ℤ))
    (fun j hj => cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      X x (d := d) hx j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j))

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
