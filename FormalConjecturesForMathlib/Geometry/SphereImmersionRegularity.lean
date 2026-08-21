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

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

public import FormalConjecturesForMathlib.Geometry.SphereImmersion

/-!
# Regularity of the canonical normal of a sphere immersion

Although Mathlib's preferred sphere charts do not give a continuous global tangent frame, the
canonical normal is regular. Locally, `inTangentCoordinates` gives a regular frame for the
derivative. Changing from that frame to the pointwise model basis scales both cross products in the
raw normal by the same determinant, so the raw normal scales by its positive square. Normalization
therefore removes the coordinate dependence. In particular, a `C^(m + 1)` immersion has a `C^m`
canonical normal.
-/

@[expose] public section

open Metric Set Function
open scoped EuclideanGeometry Manifold RealInnerProductSpace

namespace EuclideanHypersurface

private noncomputable def sphereModelBasis (p : sphere (0 : ℝ³) 1) :
    Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  sphereTangentBasis p

private noncomputable def basisDet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 2) ℝ V) (A : V →L[ℝ] V) : ℝ :=
  b.repr (A (b 0)) 0 * b.repr (A (b 1)) 1 -
    b.repr (A (b 0)) 1 * b.repr (A (b 1)) 0

private theorem euclideanCross_comp_basis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 2) ℝ V) (L : V →L[ℝ] ℝ³) (A : V →L[ℝ] V) :
    euclideanCross (L (A (b 0))) (L (A (b 1))) =
      basisDet b A • euclideanCross (L (b 0)) (L (b 1)) := by
  rw [← b.sum_repr (A (b 0)), ← b.sum_repr (A (b 1))]
  simp only [Fin.sum_univ_two, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    euclideanCross_self, smul_zero, add_zero, basisDet]
  rw [← euclideanCross_anticomm (L (b 0)) (L (b 1))]
  module

private theorem contMDiffAt_normalize
    {m : WithTop ℕ∞} {f : sphere (0 : ℝ³) 1 → ℝ³} {p : sphere (0 : ℝ³) 1}
    (hf : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m f p) (h0 : f p ≠ 0) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (fun q ↦ NormedSpace.normalize (f q)) p := by
  change ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (fun q ↦ ‖f q‖⁻¹ • f q) p
  exact (((contDiffAt_norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).comp_contMDiffAt hf).smul hf

private theorem inTangentCoordinates_sphere_eq_comp
    (G : sphere (0 : ℝ³) 1 → ℝ³) (p q : sphere (0 : ℝ³) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id G (sphereAmbientMfderiv G) p q =
      sphereAmbientMfderiv G q ∘L
        (tangentCoordChange (𝓡 2) p q q :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  rw [inTangentCoordinates_eq _ _ _ (by simpa [extChartAt_source] using hq) (by simp)]
  simp only [tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp]
  rfl

private theorem tangentCoordChange_injective
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    Function.Injective (tangentCoordChange (𝓡 2) p q q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  intro u v huv
  have hq' : q ∈ (extChartAt (𝓡 2) q).source := mem_extChartAt_source q
  have hmem : q ∈ (extChartAt (𝓡 2) p).source ∩
      (extChartAt (𝓡 2) q).source ∩ (extChartAt (𝓡 2) p).source :=
    ⟨⟨hq, hq'⟩, hq⟩
  have hu := congrArg (tangentCoordChange (𝓡 2) q p q :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) huv
  simpa only [tangentCoordChange_comp hmem, tangentCoordChange_self hq] using hu

private noncomputable def sphereNormalRawInCoordinates
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphere (0 : ℝ³) 1 → ℝ³ :=
  let b := sphereModelBasis p
  let e0 : EuclideanSpace ℝ (Fin 2) := b 0
  let e1 : EuclideanSpace ℝ (Fin 2) := b 1
  let dι := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
    (sphereAmbientMfderiv F) p
  fun q ↦ inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : ℝ³) •
    euclideanCross (dF q e0) (dF q e1)

private theorem contMDiffAt_sphereNormalRawInCoordinates
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) (m + 1) F) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormalRawInCoordinates F p) p := by
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num⟩
  let b := sphereModelBasis p
  let e0 : EuclideanSpace ℝ (Fin 2) := b 0
  let e1 : EuclideanSpace ℝ (Fin 2) := b 1
  let dι := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
    (sphereAmbientMfderiv F) p
  have hdι : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dι p :=
    (contMDiff_coe_sphere (n := 2) (m := (⊤ : WithTop ℕ∞)) p).mfderiv_const le_top
  have hdF : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dF p :=
    (hF p).mfderiv_const le_rfl
  have hdι0 := hdι.clm_apply (contMDiffAt_const :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) m (fun _ ↦ e0) p)
  have hdι1 := hdι.clm_apply (contMDiffAt_const :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) m (fun _ ↦ e1) p)
  have hdF0 := hdF.clm_apply (contMDiffAt_const :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) m (fun _ ↦ e0) p)
  have hdF1 := hdF.clm_apply (contMDiffAt_const :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) m (fun _ ↦ e1) p)
  have hcι := (euclideanCross.contMDiffAt.comp p hdι0).clm_apply hdι1
  have hcF := (euclideanCross.contMDiffAt.comp p hdF0).clm_apply hdF1
  have hp : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m
      (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p :=
    contMDiff_coe_sphere p
  have hs : ContMDiffAt (𝓡 2) 𝓘(ℝ) m
      (fun q ↦ inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : ℝ³)) p :=
    contDiff_inner.comp_contMDiffAt (hcι.prodMk_space hp)
  rw [sphereNormalRawInCoordinates]
  dsimp only
  change ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m
    (fun q ↦ inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : ℝ³) •
      euclideanCross (dF q e0) (dF q e1)) p
  exact hs.smul hcF

private theorem sphereNormalRawInCoordinates_eq_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p q : sphere (0 : ℝ³) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    sphereNormalRawInCoordinates F p q =
      basisDet (sphereModelBasis p)
          (tangentCoordChange (𝓡 2) p q q :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ^ 2 •
        sphereNormalRaw F q := by
  let b := sphereModelBasis p
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    tangentCoordChange (𝓡 2) p q q
  let dι := sphereAmbientMfderiv (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) q
  let dF := sphereAmbientMfderiv F q
  have hι := inTangentCoordinates_sphere_eq_comp
    (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) p q hq
  have hF := inTangentCoordinates_sphere_eq_comp F p q hq
  rw [sphereNormalRawInCoordinates, sphereNormalRaw]
  dsimp only
  change inner ℝ
      (euclideanCross
        ((inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
          (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))
          (sphereAmbientMfderiv (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))) p q) (b 0))
        ((inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
          (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))
          (sphereAmbientMfderiv (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))) p q) (b 1)))
      (q : ℝ³) •
        euclideanCross
          ((inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
            (sphereAmbientMfderiv F) p q) (b 0))
          ((inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
            (sphereAmbientMfderiv F) p q) (b 1)) =
      basisDet b A ^ 2 •
        (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (q : ℝ³) •
          euclideanCross (dF (b 0)) (dF (b 1)))
  rw [hι, hF]
  simp only [ContinuousLinearMap.comp_apply]
  change inner ℝ (euclideanCross (dι (A (b 0))) (dι (A (b 1)))) (q : ℝ³) •
      euclideanCross (dF (A (b 0))) (dF (A (b 1))) =
    basisDet b A ^ 2 •
      (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (q : ℝ³) •
        euclideanCross (dF (b 0)) (dF (b 1)))
  have hιcross := euclideanCross_comp_basis b dι A
  have hFcross := euclideanCross_comp_basis b dF A
  calc
    _ = inner ℝ (basisDet b A • euclideanCross (dι (b 0)) (dι (b 1))) (q : ℝ³) •
        (basisDet b A • euclideanCross (dF (b 0)) (dF (b 1))) :=
      congrArg₂ (fun (s : ℝ) (x : ℝ³) ↦ s • x)
        (congrArg (fun x ↦ inner ℝ x (q : ℝ³)) hιcross) hFcross
    _ = _ := by
      rw [real_inner_smul_left, smul_smul, smul_smul]
      congr 1
      ring

private theorem basisDet_tangentCoordChange_ne_zero
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    basisDet (sphereModelBasis p)
        (tangentCoordChange (𝓡 2) p q q :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num⟩
  let b := sphereModelBasis p
  let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    tangentCoordChange (𝓡 2) p q q
  let dι := sphereAmbientMfderiv (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) q
  have hA : Function.Injective A := tangentCoordChange_injective p q hq
  have hι : Function.Injective dι := mfderiv_coe_sphere_injective q
  have hcomp : Function.Injective (dι.comp A) := hι.comp hA
  have hLI : LinearIndependent ℝ ![(dι.comp A) (b 0), (dι.comp A) (b 1)] := by
    have hmap := b.linearIndependent.map' (dι.comp A).toLinearMap
      (LinearMap.ker_eq_bot_of_injective hcomp)
    rw [show ![(dι.comp A) (b 0), (dι.comp A) (b 1)] =
        (dι.comp A).toLinearMap ∘ b by
      funext i
      fin_cases i <;> rfl]
    exact hmap
  have hcross : euclideanCross ((dι.comp A) (b 0)) ((dι.comp A) (b 1)) ≠ 0 :=
    (euclideanCross_ne_zero_iff_linearIndependent _ _).2 hLI
  intro hdet
  apply hcross
  simp only [ContinuousLinearMap.comp_apply]
  change basisDet b A = 0 at hdet
  exact (euclideanCross_comp_basis b dι A).trans (by rw [hdet, zero_smul])

private theorem contMDiffAt_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) (m + 1) F)
    (himm : ∀ q, Function.Injective (sphereAmbientMfderiv F q)) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) p := by
  have hp : p ∈ (extChartAt (𝓡 2) p).source := mem_extChartAt_source p
  have hdet := basisDet_tangentCoordChange_ne_zero p p hp
  have hraw : sphereNormalRaw F p ≠ 0 := by
    have hn : sphereNormal F p ≠ 0 := (sphereNormal_ne_zero_iff F p).2 (himm p)
    rw [sphereNormal] at hn
    exact (not_congr (NormedSpace.normalize_eq_zero_iff _)).mp hn
  have hlocal : sphereNormalRawInCoordinates F p p ≠ 0 := by
    rw [sphereNormalRawInCoordinates_eq_smul F p p hp]
    exact smul_ne_zero (pow_ne_zero 2 hdet) hraw
  have hsmooth := contMDiffAt_normalize
    (contMDiffAt_sphereNormalRawInCoordinates F p hF) hlocal
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 2) p] with q hq
  rw [sphereNormal, sphereNormalRawInCoordinates_eq_smul F p q hq,
    NormedSpace.normalize_smul_of_pos
      (sq_pos_of_ne_zero (basisDet_tangentCoordChange_ne_zero p q hq))]

/-- A `C^(m + 1)` immersion of the unit two-sphere has a `C^m` canonical unit normal. -/
theorem contMDiff_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) (m + 1) F)
    (himm : ∀ p, Function.Injective (sphereAmbientMfderiv F p)) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) :=
  fun p ↦ contMDiffAt_sphereNormal F p hF himm

end EuclideanHypersurface
