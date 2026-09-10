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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ClosedImmersionNormalCoordinates
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentPurity
public import FormalConjecturesForMathlib.AlgebraicTopology.FlattenedSupportLocalHomology
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeCochainCone

/-!
# Constructed local relative homology for smooth closed supports

Every prescribed open neighborhood of a point on a smooth closed complex subvariety contains
an explicitly constructed smaller open neighborhood whose support-complement pair has rational
relative homology and cohomology only in degree twice the complex codimension. The comparison
and the exactly normalized normal class come from actual flattening, radial compression, and
tangent contraction. No purity, derivative, or comparison equivalence is supplied.

This is a cofinal local singular calculation. The identification with derived sheaf sections
with support, and gluing its normalizations across overlapping charts, are separate theorems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)
  (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)

/-- Restrict the constructed flattening chart by the prescribed ambient open. -/
def smoothClosedSupportRestrictionChart :
    OpenPartialHomeomorph (ComplexPoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionStandardFlatteningChart X Y i m d z).restrOpen V V.isOpen

include hzV in
theorem smoothClosedSupportRestrictionChart_mem_source :
    Point.map i z ∈
      (smoothClosedSupportRestrictionChart X Y i m d z V).source :=
  ⟨closedImmersionStandardFlatteningChart_mem_source X Y i m d z, hzV⟩

@[simp] theorem smoothClosedSupportRestrictionChart_center :
    smoothClosedSupportRestrictionChart X Y i m d z V (Point.map i z) =
      (localChart Y m z z, 0) :=
  closedImmersionStandardFlatteningChart_center X Y i m d z

theorem smoothClosedSupportRestrictionChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (smoothClosedSupportRestrictionChart X Y i m d z V).source) :
    y ∈ Set.range (Point.map i) ↔
      (smoothClosedSupportRestrictionChart X Y i m d z V y).2 = 0 :=
  closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.1

/-- An actual small open support-model neighborhood inside the prescribed open. -/
def smoothClosedSupportNeighborhood : Opens (ComplexPoint X) :=
  flattenedSupportNeighborhood (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)

theorem mem_smoothClosedSupportNeighborhood :
    Point.map i z ∈ smoothClosedSupportNeighborhood X Y i m d z V hzV :=
  mem_flattenedSupportNeighborhood _ _ _ _ _

theorem smoothClosedSupportNeighborhood_le :
    smoothClosedSupportNeighborhood X Y i m d z V hzV ≤ V :=
  fun _ hy ↦ (flattenedSupportNeighborhood_subset_source (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    hy).2

/-- The local support-complement pair, with the actual image as support. -/
abbrev smoothClosedSupportNeighborhoodPair : TopPair :=
  neighborhoodSupportComplementPair
    (smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (Set.range (Point.map i))

/-- The actual pair homeomorphism to the product normal model. -/
def smoothClosedSupportNeighborhoodPairIso :
    normalSlicePair (Fin m → ℂ) (d - m) ≅
      smoothClosedSupportNeighborhoodPair X Y i m d z V hzV :=
  flattenedSupportPairIso (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    (Set.range (Point.map i))
    (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    (congrArg Prod.snd (smoothClosedSupportRestrictionChart_center X Y i m d z V))

/-- All-degree local relative homology, computed from the actual pair maps. -/
def smoothClosedSupportRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n ≅
        RelativeHomology ℚ (standardComplexPuncturedPair (d - m)) n :=
  ((relativeHomologyFunctor ℚ n).mapIso
    (smoothClosedSupportNeighborhoodPairIso X Y i m d z V hzV).symm) ≪≫
    normalSliceRelativeHomologyIso (Fin m → ℂ) (d - m) n

theorem smoothClosedSupportRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (RelativeHomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n) :=
  (standardComplexLocalHomology_isZero_of_ne (d - m) n hn).of_iso
    (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV n)

/-- The exact complex-normal class in the actual local support pair. -/
def smoothClosedSupportNormalClass :
    RelativeHomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) (2 * (d - m)) :=
  (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
    (2 * (d - m))).inv.hom (standardComplexLocalClass (d - m))

@[simp] theorem smoothClosedSupportNormalClass_normalization :
    (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).hom.hom
      (smoothClosedSupportNormalClass X Y i m d z V hzV) =
        standardComplexLocalClass (d - m) :=
  ConcreteCategory.congr_hom
    (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).inv_hom_id _

/-- Relative cohomology uses the dual of the same actual homology map. -/
def smoothClosedSupportRelativeCohomologyEquiv (n : ℕ) :
    RelativeCohomology ℚ (standardComplexPuncturedPair (d - m)) n ≃ₗ[ℚ]
      RelativeCohomology ℚ
        (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n :=
  (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV n).toLinearEquiv.dualMap

/-- The coclass is transported from the normalized dual of the fixed complex normal
class, along the actual normal-slice equivalence. -/
def smoothClosedSupportNormalCoclass :
    RelativeCohomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV)
        (2 * (d - m)) :=
  smoothClosedSupportRelativeCohomologyEquiv X Y i m d z V hzV
    (2 * (d - m))
    (normalizedDual (standardComplexLocalClass (d - m))
      (standardComplexLocalClass_ne_zero_for_chart (d - m)))

@[simp] theorem smoothClosedSupportNormalCoclass_apply_class :
    smoothClosedSupportNormalCoclass X Y i m d z V hzV
      (smoothClosedSupportNormalClass X Y i m d z V hzV) = 1 := by
  change normalizedDual (standardComplexLocalClass (d - m))
    (standardComplexLocalClass_ne_zero_for_chart (d - m))
    ((smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
      (2 * (d - m))).hom.hom
      (smoothClosedSupportNormalClass X Y i m d z V hzV)) = 1
  rw [smoothClosedSupportNormalClass_normalization, normalizedDual_apply_self]

theorem smoothClosedSupportNormalClass_ne_zero :
    smoothClosedSupportNormalClass X Y i m d z V hzV ≠ 0 := by
  intro hzero
  have h := smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV
  rw [hzero, map_zero] at h
  exact zero_ne_one h

/-- Generation is deduced from the explicit pair computation, never used to manufacture
the normal-slice comparison. -/
theorem span_smoothClosedSupportNormalClass_eq_top :
    Submodule.span ℚ {smoothClosedSupportNormalClass X Y i m d z V hzV} = ⊤ := by
  let e := (smoothClosedSupportRelativeHomologyIso X Y i m d z V hzV
    (2 * (d - m))).symm.toLinearEquiv
  have h := congrArg (Submodule.map e.toLinearMap)
    (span_standardComplexLocalClass_eq_top_for_chart (d - m))
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h
  exact h

/-- Exact normalization uniquely specifies the local coclass, since the constructed
normal class generates the already computed local relative homology. -/
theorem smoothClosedSupportNormalCoclass_unique
    (α : RelativeCohomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV)
        (2 * (d - m)))
    (hα : α (smoothClosedSupportNormalClass X Y i m d z V hzV) = 1) :
    α = smoothClosedSupportNormalCoclass X Y i m d z V hzV :=
  (normalizedDual_unique
    (smoothClosedSupportNormalClass_ne_zero X Y i m d z V hzV)
    (span_smoothClosedSupportNormalClass_eq_top X Y i m d z V hzV) α hα).trans
      (normalizedDual_unique
        (smoothClosedSupportNormalClass_ne_zero X Y i m d z V hzV)
        (span_smoothClosedSupportNormalClass_eq_top X Y i m d z V hzV)
        _ (smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV)).symm

theorem smoothClosedSupportRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n)) := by
  have := ModuleCat.subsingleton_of_isZero
    (smoothClosedSupportRelativeHomology_isZero_of_ne X Y i m d z V hzV n hn)
  exact ModuleCat.isZero_of_subsingleton _

/-- The same concentration for the actual singular-cochain restriction cone. The cone
has its conventional unshifted grading: supported degree `n` is cone degree `n-1`. -/
theorem smoothClosedSupportCochainConeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero ((CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV))).homology
        ((n : ℤ) - 1)) :=
  (smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V hzV n hn).of_iso
    (relativeCochainConeCohomologyEquiv ℚ
      (smoothClosedSupportNeighborhoodPair X Y i m d z V hzV) n).toModuleIso

include hzV in
/-- The vanishing neighborhoods are cofinal among all ambient open neighborhoods of
the point. This is the local concentration statement needed for a stalkwise purity proof. -/
theorem exists_small_open_supportCohomology_concentrated :
    ∃ W : Opens (ComplexPoint X), Point.map i z ∈ W ∧ W ≤ V ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair W (Set.range (Point.map i))) n)) := by
  refine ⟨smoothClosedSupportNeighborhood X Y i m d z V hzV,
    mem_smoothClosedSupportNeighborhood X Y i m d z V hzV,
    smoothClosedSupportNeighborhood_le X Y i m d z V hzV, ?_⟩
  exact smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V hzV

end AlgebraicGeometry.ComplexPoint
