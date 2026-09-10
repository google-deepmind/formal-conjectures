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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexSupportedSingularModel
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSingularSectionCohomology

/-!
# Actual cohomology-sheaf concentration for smooth closed supports

The complex is the literal supported-sections kernel applied to the fixed ambient
rational injective resolution. Its open-section homology is compared to relative
singular cohomology by the actual singular resolution and restriction-cone maps.
The constructed cofinal normal neighborhoods then imply stalkwise and sheafwise
concentration in degree twice the complex codimension.

No local purity, comparison, or orientation class is supplied to the geometric theorem.
This proves concentration, not yet the normalized identification of the surviving
cohomology sheaf with rational constants on the support.
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

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Negative cohomology vanishes directly from the actual nonnegative resolution. -/
theorem complexSupportInjectiveComplex_homology_isZero_negative
    (S : Closeds (ComplexPoint X)) (n : ℤ) (hn : n < 0) :
    IsZero ((complexSupportInjectiveComplex X S).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((complexSupportInjectiveComplex X S).isZero_of_isStrictlyGE 0 n hn)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Off the support, the actual supported complex has zero cohomology stalks in every
degree: choose neighborhoods in the complement and use the defining kernel. -/
theorem complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem
    (S : Closeds (ComplexPoint X)) (x : ComplexPoint X) (hx : x ∉ S) (n : ℤ) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X)) x).obj
        ((complexSupportInjectiveComplex X S).homology n)) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hxV
  refine ⟨V ⊓ S.compl, inf_le_left, ⟨hxV, hx⟩, ?_⟩
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (TopCat.Sheaf.supportedOutsideSections_isZero_of_le
      (TopCat.of (ComplexPoint X)) S.compl (V ⊓ S.compl)
      ((ambientRationalInjectiveComplex X).X n) inf_le_right)

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The actual closed analytic image of the smooth closed immersion. -/
def smoothClosedAnalyticSupport : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), (isClosedEmbedding_map_of_closedImmersion i).isClosed_range⟩

/-- On support points, cofinal actual normal neighborhoods prove vanishing outside
twice the complex codimension, without a local-purity hypothesis. -/
theorem smoothClosedSupportInjective_homology_stalk_isZero_of_ne
    (z : ComplexPoint Y) (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X)) (Point.map i z)).obj
        ((complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).homology
          (n : ℤ))) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hzV
  let W := smoothClosedSupportNeighborhood X Y i m d z V hzV
  refine ⟨W, smoothClosedSupportNeighborhood_le X Y i m d z V hzV,
    mem_smoothClosedSupportNeighborhood X Y i m d z V hzV, ?_⟩
  let : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
        (smoothClosedAnalyticSupport X Y i : Set (ComplexPoint X))) n) :=
    ModuleCat.subsingleton_of_isZero
      (smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V hzV n hn)
  let e := complexSupportInjectiveSectionCohomologyEquiv X
    (smoothClosedAnalyticSupport X Y i) W n
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i))).homology
          (n : ℤ)) := e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The actual supported cohomology sheaf vanishes in every integer degree other than
twice the complex codimension. -/
theorem smoothClosedSupportInjective_homology_isZero_of_ne (n : ℤ)
    (hn : n ≠ 2 * ((d - m : ℕ) : ℤ)) :
    IsZero ((complexSupportInjectiveComplex X
      (smoothClosedAnalyticSupport X Y i)).homology n) := by
  by_cases hneg : n < 0
  · exact complexSupportInjectiveComplex_homology_isZero_negative X _ n hneg
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    by_cases hx : x ∈ smoothClosedAnalyticSupport X Y i
    · obtain ⟨z, rfl⟩ := hx
      exact smoothClosedSupportInjective_homology_stalk_isZero_of_ne X Y i m d z k
        (by exact_mod_cast hn)
    · exact complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem X _ x hx k

/-- The proved lower support bound, packaged in Mathlib's actual cohomological grading API. -/
theorem smoothClosedSupportInjective_isGE :
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).IsGE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne X Y i m d n (ne_of_lt hn)

/-- The proved upper support bound; together with `isGE` this is actual concentration. -/
theorem smoothClosedSupportInjective_isLE :
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).IsLE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne X Y i m d n (ne_of_gt hn)

end AlgebraicGeometry.ComplexPoint
