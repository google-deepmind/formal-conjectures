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

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.Instances.Sphere

public import FormalConjecturesForMathlib.Geometry.«3d»

/-!
# A canonical normal for immersed two-spheres in three-space

Mathlib represents every tangent space of the sphere by a copy of the fixed model space `ℝ²`.
The basis below is the standard basis of that model space, not a continuous global tangent frame.
The preferred sphere charts identify the geometric tangent plane with the model space through a
possibly orientation-reversing orthonormal map. This file constructs a normal from the corresponding
cross product and corrects its sign using the standard sphere inclusion. A change of model frame
therefore occurs in both cross products, so its determinant appears squared and the normalized
normal is independent of the chart orientation.
-/

@[expose] public section

open Metric
open scoped EuclideanGeometry Manifold RealInnerProductSpace

namespace EuclideanHypersurface

/-- The manifold derivative of a map from the unit two-sphere, with ambient codomain. -/
noncomputable def sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) F p

/-- The standard basis of Mathlib's fixed model copy of `ℝ²` for the tangent space at `p`.

This is a coordinate basis used to evaluate the manifold derivative, not a global tangent frame on
the sphere. -/
noncomputable def sphereTangentBasis (p : sphere (0 : ℝ³) 1) :
    Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) p) :=
  PiLp.basisFun 2 ℝ (Fin 2)

private theorem sphereAmbientMfderiv_inclusion_basis_apply
    (p : sphere (0 : ℝ³) 1) (i : Fin 2) :
    letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
    sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
        (sphereTangentBasis p i) =
      let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-p))).repr
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) :
        (ℝ ∙ (-(p : ℝ³)))ᗮ) : ℝ³) := by
  have : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  dsimp only
  rw [sphereAmbientMfderiv,
    ((contMDiff_coe_sphere p).mdifferentiableAt one_ne_zero).mfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-p))).repr
  change
    (fderiv ℝ ((stereoInvFunAux (-p : ℝ³) ∘
      (Subtype.val : (ℝ ∙ (-(p : ℝ³)))ᗮ → ℝ³)) ∘ U.symm)
        (stereographic' 2 (-p) p)) (PiLp.basisFun 2 ℝ (Fin 2) i) =
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) : (ℝ ∙ (-(p : ℝ³)))ᗮ) : ℝ³)
  have hp0 : stereographic' 2 (-p) p = 0 := by
    dsimp [stereographic']
    simpa [EmbeddingLike.map_eq_zero_iff] using stereographic_neg_apply p
  rw [hp0]
  have h :
      HasFDerivAt (stereoInvFunAux (-p : ℝ³) ∘
        (Subtype.val : (ℝ ∙ (-(p : ℝ³)))ᗮ → ℝ³))
        (ℝ ∙ (-(p : ℝ³)))ᗮ.subtypeL (U.symm 0) := by
    convert hasFDerivAt_stereoInvFunAux_comp_coe (-p : ℝ³)
    simp
  rw [(h.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv]
  rfl

/-- The standard model basis maps to an orthonormal frame under the derivative of the sphere
inclusion. -/
@[simp]
theorem inner_sphereAmbientMfderiv_inclusion_basis
    (p : sphere (0 : ℝ³) 1) (i j : Fin 2) :
    inner ℝ
      (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
        (sphereTangentBasis p i))
      (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
        (sphereTangentBasis p j)) =
      if i = j then 1 else 0 := by
  have : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  rw [sphereAmbientMfderiv_inclusion_basis_apply p i,
    sphereAmbientMfderiv_inclusion_basis_apply p j]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-p))).repr
  change inner ℝ
    ((ℝ ∙ (-(p : ℝ³)))ᗮ.subtypeₗᵢ (U.symm (PiLp.basisFun 2 ℝ (Fin 2) i)))
    ((ℝ ∙ (-(p : ℝ³)))ᗮ.subtypeₗᵢ (U.symm (PiLp.basisFun 2 ℝ (Fin 2) j))) = _
  rw [LinearIsometry.inner_map_map, U.symm.inner_map_map]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal i j

/-- The derivative of the sphere inclusion maps the standard model basis to an orthonormal
family. -/
theorem orthonormal_sphereAmbientMfderiv_inclusion_basis (p : sphere (0 : ℝ³) 1) :
    Orthonormal ℝ fun i : Fin 2 ↦
      sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
        (sphereTangentBasis p i) :=
  orthonormal_iff_ite.mpr (inner_sphereAmbientMfderiv_inclusion_basis p)

/-- The oriented, unnormalized normal of a map from the unit two-sphere to three-space. -/
noncomputable def sphereNormalRaw
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) : ℝ³ :=
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF := sphereAmbientMfderiv F p
  inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) •
    euclideanCross (dF (b 0)) (dF (b 1))

/-- The canonical unit normal of a map from the unit two-sphere to three-space.

Its orientation is induced by the outward orientation of the domain sphere. Thus it need not be
the outward normal of the image when `F` reverses orientation. For a non-immersion its raw normal
can vanish, in which case this definition is zero. -/
noncomputable def sphereNormal
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) : ℝ³ :=
  NormedSpace.normalize (sphereNormalRaw F p)

/-- The cross product of the inclusion frame is its radial component. -/
private theorem sphere_inclusion_cross_eq_smul (p : sphere (0 : ℝ³) 1) :
    let b := sphereTangentBasis p
    let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
    euclideanCross (dι (b 0)) (dι (b 1)) =
      inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) • (p : ℝ³) := by
  have : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  dsimp only
  refine euclideanCross_eq_inner_smul_of_orthogonal _ _ _
    (norm_eq_of_mem_sphere p) ?_ ?_
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
      range_mfderiv_coe_sphere (n := 2) p ▸ ⟨sphereTangentBasis p 0, rfl⟩
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
      range_mfderiv_coe_sphere (n := 2) p ▸ ⟨sphereTangentBasis p 1, rfl⟩

/-- The orientation factor contributed by the standard sphere inclusion has square one. -/
private theorem sphere_inclusion_orientation_factor_sq (p : sphere (0 : ℝ³) 1) :
    let b := sphereTangentBasis p
    let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
    inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) ^ 2 = 1 := by
  dsimp only
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_sphereAmbientMfderiv_inclusion_basis p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : ℝ³)
  change s ^ 2 = 1
  calc
    s ^ 2 = inner ℝ c c := by
      simp [show c = s • (p : ℝ³) from sphere_inclusion_cross_eq_smul p,
        norm_smul, norm_eq_of_mem_sphere p, pow_two]
    _ = 1 := by
      dsimp only [c]
      rw [inner_euclideanCross_euclideanCross]
      simp [hON.norm_eq_one, hON.inner_eq_zero]

/-- The raw canonical normal of the standard sphere inclusion is the radial vector. -/
@[simp]
theorem sphereNormalRaw_inclusion (p : sphere (0 : ℝ³) 1) :
    sphereNormalRaw (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p = (p : ℝ³) := by
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : ℝ³)
  change s • c = (p : ℝ³)
  rw [show c = s • (p : ℝ³) from sphere_inclusion_cross_eq_smul p,
    smul_smul, ← pow_two,
    show s ^ 2 = 1 from sphere_inclusion_orientation_factor_sq p, one_smul]

/-- The raw canonical normal is orthogonal to every image tangent vector. -/
@[simp]
theorem inner_sphereNormalRaw_sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormalRaw F p) (sphereAmbientMfderiv F p v) = 0 := by
  rw [sphereNormalRaw, real_inner_smul_left, ← (sphereTangentBasis p).sum_repr v, map_sum]
  simp [Fin.sum_univ_two, map_smul, inner_add_right, real_inner_smul_right,
    euclideanCross_inner_left, euclideanCross_inner_right, mul_zero, add_zero]

/-- The canonical normal is orthogonal to every image tangent vector, even at a non-immersion. -/
@[simp]
theorem inner_sphereNormal_sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormal F p) (sphereAmbientMfderiv F p v) = 0 := by
  rw [sphereNormal, NormedSpace.normalize, real_inner_smul_left,
    inner_sphereNormalRaw_sphereAmbientMfderiv, mul_zero]

/-- The raw canonical normal is nonzero exactly at the points where the manifold derivative is
injective. -/
private theorem sphereNormalRaw_ne_zero_iff
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphereNormalRaw F p ≠ 0 ↔ Function.Injective (sphereAmbientMfderiv F p) := by
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF := sphereAmbientMfderiv F p
  have hfactor : inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) ≠ 0 := by
    intro h
    simpa [b, dι, h] using sphere_inclusion_orientation_factor_sq p
  rw [sphereNormalRaw, smul_ne_zero_iff, and_iff_right hfactor,
    euclideanCross_ne_zero_iff_linearIndependent]
  have hfamily : dF.toLinearMap ∘ b = ![dF (b 0), dF (b 1)] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · exact fun hLI ↦ LinearMap.injective_of_linearIndependent b.span_eq (hfamily.symm ▸ hLI)
  · exact fun hF ↦ hfamily ▸ b.linearIndependent.map' dF.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hF)

/-- The canonical normal is nonzero exactly at the points where the manifold derivative is
injective. -/
theorem sphereNormal_ne_zero_iff
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphereNormal F p ≠ 0 ↔ Function.Injective (sphereAmbientMfderiv F p) := by
  simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using
    sphereNormalRaw_ne_zero_iff F p

/-- At an immersion point, the canonical normal has unit length. -/
theorem norm_sphereNormal_of_injective
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : Function.Injective (sphereAmbientMfderiv F p)) :
    ‖sphereNormal F p‖ = 1 := by
  simpa [sphereNormal] using
    NormedSpace.norm_normalize ((sphereNormalRaw_ne_zero_iff F p).mpr hF)

/-- Normalizing a positive multiple of the radial vector recovers the radial vector. -/
theorem sphereNormal_eq_of_raw_eq_pos_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) (c : ℝ) (hc : 0 < c)
    (hraw : sphereNormalRaw F p = c • (p : ℝ³)) :
    sphereNormal F p = (p : ℝ³) := by
  rw [sphereNormal, hraw, NormedSpace.normalize_smul_of_pos hc,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]

/-- A radially tangent map whose derivative is positively coercive relative to the standard
sphere inclusion has the outward radial canonical normal. -/
theorem sphereNormal_eq_radial_of_coercive
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) (c : ℝ) (hc : 0 < c)
    (hnormal : ∀ v, inner ℝ (p : ℝ³) (sphereAmbientMfderiv F p v) = 0)
    (hcoercive : ∀ v,
      c * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ (sphereAmbientMfderiv F p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v)) :
    sphereNormal F p = (p : ℝ³) := by
  have : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF := sphereAmbientMfderiv F p
  let u := dι (b 0)
  let v := dι (b 1)
  let x := dF (b 0)
  let y := dF (b 1)
  let A := inner ℝ x u
  let D := inner ℝ y v
  let P := inner ℝ x v
  let Q := inner ℝ y u
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_sphereAmbientMfderiv_inclusion_basis p
  have hApos : 0 < A := hc.trans_le <| by
    simpa [dF, dι, x, u, A, hON.norm_eq_one] using
      hcoercive (b 0)
  let s := P + Q
  let t := s • b 0 - (2 * A) • b 1
  have ht : t ≠ 0 := by
    intro ht
    have htCoord := congrArg (fun z ↦ b.repr z 1) ht
    simp [t] at htCoord
    linarith
  have hdιt : dι t ≠ 0 :=
    (map_ne_zero_iff dι (mfderiv_coe_sphere_injective p)).mpr ht
  have hquadpos : 0 < inner ℝ (dF t) (dι t) :=
    (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hdιt))).trans_le (hcoercive t)
  simp only [t, map_sub, map_smul] at hquadpos
  change 0 < inner ℝ (s • x - (2 * A) • y) (s • u - (2 * A) • v) at hquadpos
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, s, A, P, Q] at hquadpos
  have hdetAux : 0 < 4 * A * D - (P + Q) ^ 2 := by
    nlinarith
  have hdet : 0 < A * D - P * Q := by
    nlinarith [sq_nonneg (P - Q)]
  have hcrossPos : 0 < inner ℝ (euclideanCross u v) (euclideanCross x y) := by
    rw [inner_euclideanCross_euclideanCross, ← real_inner_comm u x,
      ← real_inner_comm v y, ← real_inner_comm u y,
      ← real_inner_comm v x]
    change 0 < A * D - Q * P
    simpa [mul_comm Q P] using hdet
  apply sphereNormal_eq_of_raw_eq_pos_smul F p
    (inner ℝ (euclideanCross u v) (euclideanCross x y)) hcrossPos
  change inner ℝ (euclideanCross u v) (p : ℝ³) • euclideanCross x y =
    inner ℝ (euclideanCross u v) (euclideanCross x y) • (p : ℝ³)
  rw [euclideanCross_eq_inner_smul_of_orthogonal (p : ℝ³) x y
      (norm_eq_of_mem_sphere p) (hnormal (b 0)) (hnormal (b 1)),
    real_inner_smul_right, smul_smul, mul_comm]

/-- The canonical normal of the standard sphere inclusion points radially outward. -/
@[simp]
theorem sphereNormal_inclusion (p : sphere (0 : ℝ³) 1) :
    sphereNormal (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p = (p : ℝ³) := by
  rw [sphereNormal, sphereNormalRaw_inclusion,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]

end EuclideanHypersurface
