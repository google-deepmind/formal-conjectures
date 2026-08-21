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
open scoped BigOperators EuclideanGeometry Manifold RealInnerProductSpace

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
    Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) p) := by
  unfold TangentSpace
  exact PiLp.basisFun 2 ℝ (Fin 2)

section InclusionDerivative

private local instance : Fact (Module.finrank ℝ ℝ³ = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private theorem sphereAmbientMfderiv_inclusion_basis_apply
    (p : sphere (0 : ℝ³) 1) (i : Fin 2) :
    sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
        (sphereTangentBasis p i) =
      let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
        (ne_zero_of_mem_unit_sphere (-p))).repr
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) :
        (ℝ ∙ (-(p : ℝ³)))ᗮ) : ℝ³) := by
  rw [sphereAmbientMfderiv]
  rw [((contMDiff_coe_sphere p).mdifferentiableAt one_ne_zero).mfderiv]
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
    simp only [EmbeddingLike.map_eq_zero_iff]
    apply stereographic_neg_apply
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
  rw [sphereAmbientMfderiv_inclusion_basis_apply,
    sphereAmbientMfderiv_inclusion_basis_apply]
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
        (sphereTangentBasis p i) := by
  rw [orthonormal_iff_ite]
  exact inner_sphereAmbientMfderiv_inclusion_basis p

/-- The derivative of the standard sphere inclusion preserves the coordinate inner product on
Mathlib's model tangent space. -/
theorem inner_sphereAmbientMfderiv_inclusion
    (p : sphere (0 : ℝ³) 1) (v w : TangentSpace (𝓡 2) p) :
    inner ℝ
      (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v)
      (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p w) =
      ∑ i, (sphereTangentBasis p).repr v i * (sphereTangentBasis p).repr w i := by
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  have horth (i j : Fin 2) : inner ℝ (dι (b i)) (dι (b j)) =
      if i = j then 1 else 0 := by
    exact inner_sphereAmbientMfderiv_inclusion_basis p i j
  change inner ℝ (dι v) (dι w) = ∑ i, b.repr v i * b.repr w i
  calc
    _ = inner ℝ (dι (∑ i, b.repr v i • b i)) (dι (∑ i, b.repr w i • b i)) := by
      rw [b.sum_repr, b.sum_repr]
    _ = _ := by
      rw [map_sum, map_sum]
      simp_rw [inner_sum, sum_inner, map_smul, real_inner_smul_left,
        real_inner_smul_right]
      simp_rw [horth]
      simp [Fin.sum_univ_two]

end InclusionDerivative

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

/-- The orientation factor contributed by the standard sphere inclusion is nonzero. -/
private theorem sphereInclusionOrientationFactor_ne_zero (p : sphere (0 : ℝ³) 1) :
    inner ℝ
      (euclideanCross
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
          (sphereTangentBasis p 0))
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
          (sphereTangentBasis p 1)))
      (p : ℝ³) ≠ 0 := by
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  change inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : ℝ³) ≠ 0
  have hι : Function.Injective dι := mfderiv_coe_sphere_injective p
  have hιLI : LinearIndependent ℝ ![dι (b 0), dι (b 1)] := by
    have hmap := b.linearIndependent.map' dι.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hι)
    rw [show ![dι (b 0), dι (b 1)] = dι.toLinearMap ∘ b by
      funext i
      fin_cases i <;> rfl]
    exact hmap
  have hcross : euclideanCross (dι (b 0)) (dι (b 1)) ≠ 0 :=
    (euclideanCross_ne_zero_iff_linearIndependent _ _).2 hιLI
  have hp : ‖(p : ℝ³)‖ = 1 := norm_eq_of_mem_sphere p
  have horth (i : Fin 2) : inner ℝ (p : ℝ³) (dι (b i)) = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← range_mfderiv_coe_sphere (n := 2) p]
    exact ⟨b i, rfl⟩
  intro hfactor
  apply hcross
  rw [euclideanCross_eq_inner_smul_of_orthogonal (p : ℝ³) _ _ hp (horth 0) (horth 1),
    hfactor, zero_smul]

/-- The raw canonical normal is orthogonal to every image tangent vector. -/
@[simp]
theorem inner_sphereNormalRaw_sphereAmbientMfderiv
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormalRaw F p) (sphereAmbientMfderiv F p v) = 0 := by
  rw [sphereNormalRaw]
  dsimp only
  rw [real_inner_smul_left]
  apply mul_eq_zero_of_right
  rw [← (sphereTangentBasis p).sum_repr v]
  rw [map_sum]
  simp only [Fin.sum_univ_two, map_smul, inner_add_right, real_inner_smul_right,
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
  let dF := sphereAmbientMfderiv F p
  have hfactor := sphereInclusionOrientationFactor_ne_zero p
  rw [sphereNormalRaw]
  dsimp only
  rw [smul_ne_zero_iff, and_iff_right hfactor,
    euclideanCross_ne_zero_iff_linearIndependent]
  have hfamily : dF.toLinearMap ∘ b = ![dF (b 0), dF (b 1)] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro hLI
    apply LinearMap.injective_of_linearIndependent b.span_eq
    rw [hfamily]
    exact hLI
  · intro hF
    have hmap := b.linearIndependent.map' dF.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hF)
    rwa [hfamily] at hmap

/-- The canonical normal is nonzero exactly at the points where the manifold derivative is
injective. -/
theorem sphereNormal_ne_zero_iff
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) :
    sphereNormal F p ≠ 0 ↔ Function.Injective (sphereAmbientMfderiv F p) := by
  rw [sphereNormal]
  exact (not_congr (NormedSpace.normalize_eq_zero_iff _)).trans
    (sphereNormalRaw_ne_zero_iff F p)

/-- At an immersion point, the canonical normal has unit length. -/
theorem norm_sphereNormal_of_injective
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1)
    (hF : Function.Injective (sphereAmbientMfderiv F p)) :
    ‖sphereNormal F p‖ = 1 := by
  rw [sphereNormal]
  exact NormedSpace.norm_normalize ((sphereNormalRaw_ne_zero_iff F p).mpr hF)

/-- Normalizing a positive multiple of the radial vector recovers the radial vector. -/
theorem sphereNormal_eq_of_raw_eq_pos_smul
    (F : sphere (0 : ℝ³) 1 → ℝ³) (p : sphere (0 : ℝ³) 1) (c : ℝ) (hc : 0 < c)
    (hraw : sphereNormalRaw F p = c • (p : ℝ³)) :
    sphereNormal F p = (p : ℝ³) := by
  rw [sphereNormal, hraw, NormedSpace.normalize_smul_of_pos hc,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]

/-- The canonical normal of the standard sphere inclusion points radially outward. -/
@[simp]
theorem sphereNormal_inclusion (p : sphere (0 : ℝ³) 1) :
    sphereNormal (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p = (p : ℝ³) := by
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  let b := sphereTangentBasis p
  let dι := sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : ℝ³)
  have hp : ‖(p : ℝ³)‖ = 1 := norm_eq_of_mem_sphere p
  have horth (i : Fin 2) : inner ℝ (p : ℝ³) (dι (b i)) = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← range_mfderiv_coe_sphere (n := 2) p]
    exact ⟨b i, rfl⟩
  have hc : c = s • (p : ℝ³) := by
    exact euclideanCross_eq_inner_smul_of_orthogonal
      (p : ℝ³) (dι (b 0)) (dι (b 1)) hp (horth 0) (horth 1)
  have hs : s ≠ 0 := by
    exact sphereInclusionOrientationFactor_ne_zero p
  apply sphereNormal_eq_of_raw_eq_pos_smul _ p (s ^ 2) (sq_pos_of_ne_zero hs)
  rw [sphereNormalRaw]
  dsimp only
  change s • c = s ^ 2 • (p : ℝ³)
  rw [hc, smul_smul, pow_two]

end EuclideanHypersurface
