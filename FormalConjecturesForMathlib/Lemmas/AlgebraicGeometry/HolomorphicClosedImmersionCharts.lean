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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HolomorphicClosedImmersionCharts

/-!
# Actual holomorphic support-flattening charts

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HolomorphicClosedImmersionCharts`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
  (e : OpenPartialHomeomorph E F)

@[simp] theorem biAnalyticRestrict_apply (x : E) : e.biAnalyticRestrict x = e x := rfl
@[simp] theorem biAnalyticRestrict_symm_apply (y : F) : e.biAnalyticRestrict.symm y = e.symm y := rfl

end OpenPartialHomeomorph

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

theorem closedImmersionNormalCoordinateChange_mem_source :
    localChart X d (Point.map i z) (Point.map i z) ∈
      (closedImmersionNormalCoordinateChange X Y i m d z).source :=
  ⟨closedImmersionNormalChart_mem_target X Y i m d z, trivial⟩

@[simp] theorem closedImmersionNormalCoordinateChange_center :
    closedImmersionNormalCoordinateChange X Y i m d z
      (localChart X d (Point.map i z) (Point.map i z)) =
        (localChart Y m z z, 0) := by
  change closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
    ((closedImmersionNormalChart X Y i m d z).symm _) = _
  rw [closedImmersionNormalChart_symm_center]
  simp [closedImmersionNormalCoordinatesLinearEquiv]

theorem analyticAt_closedImmersionNormalCoordinateChange :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z)
      (localChart X d (Point.map i z) (Point.map i z)) :=
  ((closedImmersionNormalCoordinatesLinearEquiv X Y i m d z).toContinuousLinearMap.analyticAt
    _).comp (analyticAt_closedImmersionNormalChart_symm X Y i m d z)

theorem analyticAt_closedImmersionNormalCoordinateChange_symm :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
      (localChart Y m z z, 0) := by
  let K := closedImmersionNormalCoordinatesLinearEquiv X Y i m d z
  have hK : K.symm (localChart Y m z z, 0) = (localChart Y m z z, 0) := by
    simp [K, closedImmersionNormalCoordinatesLinearEquiv]
  have hA' : AnalyticAt ℂ (closedImmersionNormalChart X Y i m d z)
      (K.symm (localChart Y m z z, 0)) := hK ▸ analyticAt_closedImmersionNormalChart X Y i m d z
  exact hA'.comp (K.symm.toContinuousLinearMap.analyticAt _)

@[simp] theorem closedImmersionHolomorphicFlatteningChart_apply (y : ComplexPoint X) :
    closedImmersionHolomorphicFlatteningChart X Y i m d z y =
      closedImmersionStandardFlatteningChart X Y i m d z y := rfl

@[simp] theorem closedImmersionHolomorphicFlatteningChart_symm_apply
    (v : (Fin m → ℂ) × (Fin (d - m) → ℂ)) :
    (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v =
      (localChart X d (Point.map i z)).symm
        ((closedImmersionNormalCoordinateChange X Y i m d z).symm v) := rfl

theorem closedImmersionHolomorphicFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionHolomorphicFlatteningChart X Y i m d z).source := by
  refine ⟨⟨mem_localChart_source X d (Point.map i z), ?_⟩,
    closedImmersionStandardFlatteningChart_mem_source X Y i m d z⟩
  apply (OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mpr
  refine ⟨closedImmersionNormalCoordinateChange_mem_source X Y i m d z,
    analyticAt_closedImmersionNormalCoordinateChange X Y i m d z, ?_⟩
  simp only [OpenPartialHomeomorph.symm_symm]
  rw [closedImmersionNormalCoordinateChange_center]
  exact analyticAt_closedImmersionNormalCoordinateChange_symm X Y i m d z

@[simp] theorem closedImmersionHolomorphicFlatteningChart_center :
    closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z) =
      (localChart Y m z z, 0) :=
  closedImmersionStandardFlatteningChart_center X Y i m d z

variable (z' : ComplexPoint Y)

@[simp] theorem closedImmersionNormalTransitionDerivativeEquiv_apply (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition X Y i m d z z').source)
    (v : Fin (d - m) → ℂ) :
    closedImmersionNormalTransitionDerivativeEquiv X Y i m d z z' a ha v =
      (fderiv ℂ (closedImmersionNormalTransition X Y i m d z z')
        (a, 0) (0, v)).2 := rfl

/-- On a smaller transverse normal neighborhood in a genuine overlap, transition and
inclusion have exactly the same top relative-cohomology pullback. All holomorphic and
normal-derivative facts are obtained from the constructed closed-immersion charts. -/
theorem exists_open_closedImmersionNormalTransition_coclass_invariance (a : Fin m → ℂ)
    (ha : (a, 0) ∈ (closedImmersionNormalTransition X Y i m d z z').source) :
    let T := closedImmersionNormalTransition X Y i m d z z'
    let h0 : normalTransitionMap (d - m) T a 0 = 0 :=
      (closedImmersionNormalTransition_preserves_support X Y i m d z z'
        (a, 0) ha).mpr rfl
    ∃ (W : Set (Fin (d - m) → ℂ)) (hW : W ⊆ normalTransitionDomain (d - m) T a)
      (hne : ∀ v, v ∈ W → v ≠ 0 → normalTransitionMap (d - m) T a v ≠ 0),
      IsOpen W ∧ 0 ∈ W ∧
      relativeCohomologyMap ℚ (2 * (d - m))
        (complexNeighborhoodPuncturedPairMapOf (d - m) W (normalTransitionMap (d - m) T a)
          ((normalTransitionMap_continuousOn (d - m) T a).mono hW) h0 hne) =
        relativeCohomologyMap ℚ (2 * (d - m)) (neighborhoodPointComplementPairMap W 0) :=
  exists_open_normalTransition_relativeCohomologyMap_eq (d - m)
    (closedImmersionNormalTransition X Y i m d z z') a ha
    (closedImmersionNormalTransition_preserves_support X Y i m d z z')
    (analyticAt_closedImmersionNormalTransition X Y i m d z z' (a, 0) ha)
    (analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (a, 0) ha)

end AlgebraicGeometry.ComplexPoint
