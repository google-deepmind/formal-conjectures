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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAnalyticMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Analytic local left inverses from actual section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts. In particular derivative injectivity is proved, not supplied as
an immersion or purity field.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- Any family of sections on an intrinsic open lifts, after restriction, on a single
affine ambient neighborhood of the selected point. The lifts come from the actual
surjective closed-immersion map on affine sections. -/
theorem Scheme.Hom.exists_affine_local_section_lifts
    {J : Type*} (V : Y.Opens) (s : J → Γ(Y, V)) (y : Y) (hy : y ∈ V) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hUV : i ⁻¹ᵁ U ≤ V),
      i y ∈ U ∧ ∃ r : J → Γ(X, U),
        ∀ j, i.app U (r j) = Y.presheaf.map (homOfLE hUV).op (s j) := by
  obtain ⟨W, hW, hpre⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hyW : i y ∈ W := show y ∈ ⇑i ⁻¹' W from hpre ▸ hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyW hW
  have hUV : i ⁻¹ᵁ U ≤ V := fun z hz ↦ show z ∈ (V : Set Y) from hpre ▸ hUW hz
  choose r hr using fun j => i.app_surjective U hU
    (Y.presheaf.map (homOfLE hUV).op (s j))
  exact ⟨U, hU, hUV, hyU, r, hr⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

/-- The actual inclusion written in the canonical intrinsic and ambient complex charts. -/
def inclusionInComplexCharts (z : ComplexPoint Y) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => localChart X d (Point.map i z)
    (Point.map i ((localChart Y m z).symm v))

@[simp] theorem inclusionInComplexCharts_at_center (z : ComplexPoint Y) :
    inclusionInComplexCharts X Y i m d z
      (localChart Y m z z) =
        localChart X d (Point.map i z) (Point.map i z) := by
  unfold inclusionInComplexCharts
  rw [(localChart Y m z).left_inv (mem_localChart_source Y m z)]

/-- Analyticity is inherited from the actual morphism of smooth schemes. -/
theorem analyticAt_inclusionInComplexCharts (z : ComplexPoint Y) :
    AnalyticAt ℂ (inclusionInComplexCharts X Y i m d z)
      (localChart Y m z z) := by
  apply analyticAt_localChart_symm_map Y X i m d z
    ((localChart Y m z).map_source (mem_localChart_source Y m z))
  rw [(localChart Y m z).left_inv (mem_localChart_source Y m z)]
  exact mem_localChart_source X d (Point.map i z)

/-- A smooth closed immersion has an actual analytic local left inverse in complex
coordinates. It is constructed by lifting the intrinsic coordinate sections, not assumed
from an analytic-immersion structure. -/
theorem exists_analytic_localLeftInverse_of_isClosedImmersion [IsClosedImmersion i.left]
    (z : ComplexPoint Y) :
    ∃ L : (Fin d → ℂ) → (Fin m → ℂ),
      AnalyticAt ℂ L
        (inclusionInComplexCharts X Y i m d z
          (localChart Y m z z)) ∧
      (L ∘ inclusionInComplexCharts X Y i m d z) =ᶠ[
        𝓝 (localChart Y m z z)] id := by
  let D := localEtaleCoordinates Y m z
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using
      mem_localEtaleCoordinates Y m z
  obtain ⟨U, _hU, hUV, hzU, r, hr⟩ := i.left.exists_affine_local_section_lifts
    D.ambientCoordinateOpen D.ambientCoordinateSection z.underlying hzD
  let eY := localChart Y m z
  let eX := localChart X d (Point.map i z)
  let L : (Fin d → ℂ) → (Fin m → ℂ) :=
    fun w j => Point.evaluate U (r j) (eX.symm w)
  have hzY : z ∈ eY.source := mem_localChart_source Y m z
  have hzX : Point.map i z ∈ eX.source :=
    mem_localChart_source X d (Point.map i z)
  have hzYt : eY z ∈ eY.target := eY.map_source hzY
  have hzXt : eX (Point.map i z) ∈ eX.target := eX.map_source hzX
  refine ⟨L, ?_, ?_⟩
  · rw [inclusionInComplexCharts_at_center]
    refine AnalyticAt.pi fun j ↦ ?_
    apply analyticAt_localChart_symm_evaluate X d (Point.map i z) hzXt U (r j)
    change eX.symm (eX (Point.map i z)) ∈ Point.overOpen U
    rw [eX.left_inv hzX]
    exact hzU
  · have hc : ContinuousAt (fun v => Point.map i (eY.symm v)) (eY z) :=
      (Point.continuous_map i).continuousAt.comp (eY.continuousAt_symm hzYt)
    have hX : ∀ᶠ v in 𝓝 (eY z), Point.map i (eY.symm v) ∈ eX.source := by
      apply hc (eX.open_source.mem_nhds _)
      change Point.map i (eY.symm (eY z)) ∈ eX.source
      rw [eY.left_inv hzY]
      exact hzX
    have hU : ∀ᶠ v in 𝓝 (eY z), Point.map i (eY.symm v) ∈ Point.overOpen U := by
      apply hc ((Point.isOpen_overOpen U).mem_nhds _)
      change Point.map i (eY.symm (eY z)) ∈ Point.overOpen U
      rw [eY.left_inv hzY]
      exact hzU
    filter_upwards [eY.open_target.mem_nhds hzYt, hX, hU] with v hvY hvX hvU
    funext j
    change Point.evaluate U (r j)
      (eX.symm (eX (Point.map i (eY.symm v)))) = v j
    rw [eX.left_inv hvX, Point.evaluate_map, hr,
      ← Point.evaluate_res hUV (D.ambientCoordinateSection j) (eY.symm v)
        ((Point.mem_overOpen_map_iff i _ U).mp hvU),
      ← localChart_apply_component_eq_evaluate Y m z (eY.symm v) (eY.map_target hvY) j]
    exact congrFun (eY.right_inv hvY) j

/-- The derivative of a smooth closed immersion has an actual continuous-linear left
inverse, obtained by differentiating the constructed analytic local left inverse. -/
theorem exists_leftInverse_fderiv_inclusionInComplexCharts [IsClosedImmersion i.left]
    (z : ComplexPoint Y) :
    ∃ P : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ),
      P.comp (fderiv ℂ (inclusionInComplexCharts X Y i m d z)
        (localChart Y m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
  obtain ⟨L, hL, hleft⟩ :=
    exists_analytic_localLeftInverse_of_isClosedImmersion X Y i m d z
  let φ := inclusionInComplexCharts X Y i m d z
  let a := localChart Y m z z
  refine ⟨fderiv ℂ L (φ a), ?_⟩
  have hφ := analyticAt_inclusionInComplexCharts X Y i m d z
  have hc := hL.differentiableAt.hasFDerivAt.comp a hφ.differentiableAt.hasFDerivAt
  exact (hc.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id a)

/-- Derivative injectivity for the actual chart-written closed immersion, with no
assumed immersion, cotangent comparison, regular-sequence, or flattening data. -/
theorem injective_fderiv_inclusionInComplexCharts [IsClosedImmersion i.left]
    (z : ComplexPoint Y) :
    Function.Injective
      (fderiv ℂ (inclusionInComplexCharts X Y i m d z)
        (localChart Y m z z)) := by
  obtain ⟨P, hP⟩ :=
    exists_leftInverse_fderiv_inclusionInComplexCharts X Y i m d z
  exact Function.LeftInverse.injective (g := P) fun v ↦ DFunLike.congr_fun hP v

end AlgebraicGeometry.ComplexPoint
