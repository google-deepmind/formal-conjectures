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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
public import FormalConjecturesForMathlib.Geometry.Manifold.Orientation
public import FormalConjecturesForMathlib.LinearAlgebra.ComplexOrientation
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# The complex orientation of the manifold of complex points

This file keeps orientation-specific results out of the statement-facing `Lemmas` layer. It
constructs the canonical real manifold orientation of a smooth complex analytification from
holomorphic chart changes and the standard orientation of complex vector space.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- After restricting scalars, smooth complex points form a real `C¹` manifold on the same
underlying charts. This is the real-manifold structure to which the orientation API of
[mathlib4 PR #35376](https://github.com/leanprover-community/mathlib4/pull/35376) applies. -/
instance isRealManifold_one [SmoothOfRelativeDimension d X.hom] :
    IsManifold 𝓘(ℝ, Fin d → ℂ) 1 (ComplexPoint X) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  have h := (contDiffOn_localChart_transition X d z z').restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, Function.id_comp, Function.comp_id, Set.preimage_id,
    Set.range_id, Set.inter_univ] using h.of_le (by simp)

/-- On the overlap of two algebraic complex charts, the real tangent coordinate change is the
restriction of scalars of the complex tangent coordinate change. -/
lemma realTangentCoordChange_eq_restrictScalars
    [SmoothOfRelativeDimension d X.hom]
    (x y z : ComplexPoint X)
    (hx : z ∈ (localChart X d x).source)
    (hy : z ∈ (localChart X d y).source) :
    tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x y z =
      (tangentCoordChange 𝓘(ℂ, Fin d → ℂ) x y z).restrictScalars ℝ := by
  have hoverlapR : z ∈ (extChartAt 𝓘(ℝ, Fin d → ℂ) x).source ∩
      (extChartAt 𝓘(ℝ, Fin d → ℂ) y).source := by
    rw [extChartAt_source, extChartAt_source]
    change z ∈ (localChart X d x).source ∩
      (localChart X d y).source
    exact ⟨hx, hy⟩
  have hoverlapC : z ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) x).source ∩
      (extChartAt 𝓘(ℂ, Fin d → ℂ) y).source := by
    rw [extChartAt_source, extChartAt_source]
    change z ∈ (localChart X d x).source ∩
      (localChart X d y).source
    exact ⟨hx, hy⟩
  have hR := hasFDerivWithinAt_tangentCoordChange
    (I := 𝓘(ℝ, Fin d → ℂ)) hoverlapR
  have hC := (hasFDerivWithinAt_tangentCoordChange
    (I := 𝓘(ℂ, Fin d → ℂ)) hoverlapC).restrictScalars ℝ
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id] at hR hC
  exact uniqueDiffWithinAt_univ.eq hR hC

/-- The real tangent coordinate equivalence on a chart overlap is the restriction of scalars of
the corresponding complex tangent coordinate equivalence. -/
lemma realTangentCoordChangeEquiv_toLinearMap_eq_restrictScalars
    [SmoothOfRelativeDimension d X.hom]
    (x y z : ComplexPoint X)
    (hx : z ∈ (localChart X d x).source)
    (hy : z ∈ (localChart X d y).source) :
    (tangentCoordChangeEquiv 𝓘(ℝ, Fin d → ℂ) x y z).toLinearMap =
      ((tangentCoordChangeEquiv 𝓘(ℂ, Fin d → ℂ) x y z).restrictScalars ℝ).toLinearMap := by
  calc
    (tangentCoordChangeEquiv 𝓘(ℝ, Fin d → ℂ) x y z).toLinearMap =
        (tangentCoordChange 𝓘(ℝ, Fin d → ℂ) x y z).toLinearMap :=
      tangentCoordChangeEquiv_toLinearMap hx hy
    _ = ((tangentCoordChange 𝓘(ℂ, Fin d → ℂ) x y z).restrictScalars ℝ).toLinearMap :=
      congrArg ContinuousLinearMap.toLinearMap
        (realTangentCoordChange_eq_restrictScalars X d x y z hx hy)
    _ = ((tangentCoordChangeEquiv 𝓘(ℂ, Fin d → ℂ) x y z).restrictScalars ℝ).toLinearMap := by
      change LinearMap.restrictScalars ℝ
          (tangentCoordChange 𝓘(ℂ, Fin d → ℂ) x y z).toLinearMap =
        LinearMap.restrictScalars ℝ
          (tangentCoordChangeEquiv 𝓘(ℂ, Fin d → ℂ) x y z).toLinearMap
      exact congrArg (LinearMap.restrictScalars ℝ)
        (tangentCoordChangeEquiv_toLinearMap
          (I := 𝓘(ℂ, Fin d → ℂ)) hx hy).symm

/-- The real determinant of every tangent coordinate change between the algebraic holomorphic
charts is positive. -/
lemma realTangentCoordChangeEquiv_det_pos
    [SmoothOfRelativeDimension d X.hom]
    (x y z : ComplexPoint X)
    (hx : z ∈ (localChart X d x).source)
    (hy : z ∈ (localChart X d y).source) :
    0 < LinearMap.det
      (tangentCoordChangeEquiv 𝓘(ℝ, Fin d → ℂ) x y z).toLinearMap := by
  rw [realTangentCoordChangeEquiv_toLinearMap_eq_restrictScalars
    X d x y z hx hy]
  exact LinearEquiv.det_restrictScalars_complex_pos
    (tangentCoordChangeEquiv 𝓘(ℂ, Fin d → ℂ) x y z)

/-- The constant-sign lift of the complex orientation on a smooth complex analytification.

The model orientation is the ordered real/imaginary orientation of `Fin d → ℂ`; every preferred
holomorphic chart has sign `1`. Compatibility is the positivity of the real determinant of the
complex-linear tangent coordinate change. -/
def orientationLift [SmoothOfRelativeDimension d X.hom] :
    Manifold.OrientationLift 𝓘(ℝ, Fin d → ℂ) (ComplexPoint X) (Fin (d * 2)) where
  modelOrientation := Complex.piOrientation d
  chartSign _ _ := 1
  continuousOn_chartSign _ := continuousOn_const
  chartSign_eq_one_of_notMem _ _ _ := rfl
  compatible x y z hx hy := by
    simp only [Manifold.signedOrientation_one]
    exact (Orientation.map_eq_iff_det_pos (Complex.piOrientation d)
      (tangentCoordChangeEquiv 𝓘(ℝ, Fin d → ℂ) x y z) Fact.out).2
        (realTangentCoordChangeEquiv_det_pos X d x y z hx hy)

/-- The complex orientation on a smooth complex analytification. -/
def manifoldOrientation [SmoothOfRelativeDimension d X.hom] :
    Manifold.Orientation 𝓘(ℝ, Fin d → ℂ) (ComplexPoint X) (Fin (d * 2)) :=
  Manifold.Orientation.mk (orientationLift X d)

/-- Smooth complex analytifications carry their canonical complex orientation as a real
manifold. -/
instance orientedManifold [SmoothOfRelativeDimension d X.hom] :
    Manifold.OrientedManifold 𝓘(ℝ, Fin d → ℂ)
      (ComplexPoint X) (Fin (d * 2)) where
  manifoldOrientation := manifoldOrientation X d

end AlgebraicGeometry.ComplexPoint
