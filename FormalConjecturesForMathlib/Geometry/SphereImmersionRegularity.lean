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

Although the sphere charts do not give a continuous global tangent frame, `sphereNormal` is
regular. In local tangent coordinates, a frame change scales its raw normal by a positive square,
which normalization removes. Thus a `C^(m + 1)` immersion has a `C^m` canonical normal.
-/

@[expose] public section

open Metric
open scoped EuclideanGeometry EuclideanSpace Manifold RealInnerProductSpace

namespace EuclideanHypersurface

private theorem euclideanCross_comp_basis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 2) ℝ V) (L : V →L[ℝ] ℝ³) (A : V →L[ℝ] V) :
    euclideanCross (L (A (b 0))) (L (A (b 1))) =
      LinearMap.det A.toLinearMap • euclideanCross (L (b 0)) (L (b 1)) := by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two,
    ← b.sum_repr (A (b 0)), ← b.sum_repr (A (b 1))]
  simp only [Fin.sum_univ_two, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, euclideanCross_self, smul_zero, add_zero,
    LinearMap.toMatrix_apply]
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
    inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id G
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) G) p q =
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) G q ∘L
        (tangentCoordChange (𝓡 2) p q q :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  rw [inTangentCoordinates_eq _ _ _ (by simpa [extChartAt_source] using hq) (by simp),
    tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp]
  rfl

private theorem tangentCoordChange_injective
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    Function.Injective (tangentCoordChange (𝓡 2) p q q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  intro u v huv
  have hmem : q ∈ (extChartAt (𝓡 2) p).source ∩
      (extChartAt (𝓡 2) q).source ∩ (extChartAt (𝓡 2) p).source :=
    ⟨⟨hq, mem_extChartAt_source q⟩, hq⟩
  simpa only [tangentCoordChange_comp hmem, tangentCoordChange_self hq] using
    congrArg (tangentCoordChange (𝓡 2) q p q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) huv

private noncomputable def sphereNormalRawInCoordinates
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphere (0 : ℝ³) 1 → ℝ³ :=
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F) p
  fun q ↦ inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : ℝ³) •
    euclideanCross (dF q e0) (dF q e1)

private theorem contMDiffAt_sphereNormalRawInCoordinates
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) n F p) (hmn : m + 1 ≤ n) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormalRawInCoordinates F p) p := by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
    (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))) p
  let dF := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F) p
  have hdι : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dι p :=
    (contMDiff_coe_sphere (n := 2) (m := ⊤) p).mfderiv_const le_top
  have hdF : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ³) m dF p :=
    hF.mfderiv_const hmn
  have hdι0 := hdι.clm_apply (contMDiffAt_const (c := e0))
  have hdι1 := hdι.clm_apply (contMDiffAt_const (c := e1))
  have hdF0 := hdF.clm_apply (contMDiffAt_const (c := e0))
  have hdF1 := hdF.clm_apply (contMDiffAt_const (c := e1))
  have hcι := (euclideanCross.contMDiffAt.comp p hdι0).clm_apply hdι1
  have hcF := (euclideanCross.contMDiffAt.comp p hdF0).clm_apply hdF1
  simpa [sphereNormalRawInCoordinates, b, e0, e1, dι, dF] using
    (contDiff_inner.comp_contMDiffAt
      (hcι.prodMk_space (contMDiff_coe_sphere p))).smul hcF

private theorem sphereNormalRawInCoordinates_eq_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p q : sphere (0 : ℝ³) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    sphereNormalRawInCoordinates F p q =
      LinearMap.det (tangentCoordChange (𝓡 2) p q q :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ^ 2 •
        sphereNormalRaw F q := by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let A := tangentCoordChange (𝓡 2) p q q
  let dι : TangentSpace (𝓡 2) q →L[ℝ] ℝ³ :=
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) q
  let dF : TangentSpace (𝓡 2) q →L[ℝ] ℝ³ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F q
  let dιc := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id
    (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³))) p q
  let dFc := inTangentCoordinates (𝓡 2) 𝓘(ℝ, ℝ³) id F
    (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F) p q
  rw [sphereNormalRaw]
  rw [sphereTangentBasis_apply q 0, sphereTangentBasis_apply q 1]
  change inner ℝ (euclideanCross (dιc (b 0)) (dιc (b 1))) (q : ℝ³) •
      euclideanCross (dFc (b 0)) (dFc (b 1)) =
      LinearMap.det A.toLinearMap ^ 2 •
        (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (q : ℝ³) •
          euclideanCross (dF (b 0)) (dF (b 1)))
  rw [show dιc = dι.comp A from inTangentCoordinates_sphere_eq_comp
      (fun r : sphere (0 : ℝ³) 1 ↦ (r : ℝ³)) p q hq,
    show dFc = dF.comp A from inTangentCoordinates_sphere_eq_comp F p q hq]
  calc
    _ = inner ℝ (LinearMap.det A.toLinearMap • euclideanCross (dι (b 0)) (dι (b 1)))
          (q : ℝ³) •
        (LinearMap.det A.toLinearMap • euclideanCross (dF (b 0)) (dF (b 1))) :=
      congrArg₂ (fun (s : ℝ) (x : ℝ³) ↦ s • x)
        (congrArg (fun x ↦ inner ℝ x (q : ℝ³)) (euclideanCross_comp_basis b dι A))
        (euclideanCross_comp_basis b dF A)
    _ = _ := by
      rw [real_inner_smul_left]
      module

private theorem det_tangentCoordChange_ne_zero
    (p q : sphere (0 : ℝ³) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    LinearMap.det (tangentCoordChange (𝓡 2) p q q :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ≠ 0 := by
  simpa [LinearMap.det_eq_zero_iff_ker_ne_bot] using
    LinearMap.ker_eq_bot_of_injective (tangentCoordChange_injective p q hq)

/-- At an immersion point, a locally `C^n` map has a locally `C^m` canonical unit normal when
`m + 1 ≤ n`. -/
theorem contMDiffAt_sphereNormal_of_le
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) n F p) (hmn : m + 1 ≤ n)
    (himm : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p)) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) p := by
  have hp : p ∈ (extChartAt (𝓡 2) p).source := mem_extChartAt_source p
  have hlocal : sphereNormalRawInCoordinates F p p ≠ 0 := by
    rw [sphereNormalRawInCoordinates_eq_smul F p p hp]
    refine smul_ne_zero (pow_ne_zero 2 (det_tangentCoordChange_ne_zero p p hp)) ?_
    simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using
      (sphereNormal_ne_zero_iff F p).2 himm
  apply (contMDiffAt_normalize
    (contMDiffAt_sphereNormalRawInCoordinates F p hF hmn) hlocal).congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 2) p] with q hq
  rw [sphereNormal, sphereNormalRawInCoordinates_eq_smul F p q hq,
    NormedSpace.normalize_smul_of_pos
      (sq_pos_of_ne_zero (det_tangentCoordChange_ne_zero p q hq))]

/-- At an immersion point, a locally `C^(m + 1)` map has a locally `C^m` canonical unit normal. -/
theorem contMDiffAt_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) (m + 1) F p)
    (himm : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p)) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) p :=
  contMDiffAt_sphereNormal_of_le F p hF le_rfl himm

/-- A `C^n` immersion of the unit two-sphere has a `C^m` canonical unit normal when
`m + 1 ≤ n`. -/
theorem contMDiff_sphereNormal_of_le
    {m n : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) n F) (hmn : m + 1 ≤ n)
    (himm : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p)) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) :=
  fun p ↦ contMDiffAt_sphereNormal_of_le F p (hF p) hmn (himm p)

/-- A `C^(m + 1)` immersion of the unit two-sphere has a `C^m` canonical unit normal. -/
theorem contMDiff_sphereNormal
    {m : WithTop ℕ∞} (F : sphere (0 : ℝ³) 1 → ℝ³)
    (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) (m + 1) F)
    (himm : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p)) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ³) m (sphereNormal F) :=
  contMDiff_sphereNormal_of_le F hF le_rfl himm

end EuclideanHypersurface
