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

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Extrinsic fundamental forms in Euclidean space

The second fundamental form uses `II(v, w) = -⟪dn(v), dF(w)⟫`, so `dn = c • dF` corresponds
to `II = (-c) • I`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace EuclideanHypersurface

variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first fundamental form induced by `dF`. -/
noncomputable def firstFundamentalFormAt (dF : V →L[ℝ] E) : LinearMap.BilinForm ℝ V :=
  LinearMap.BilinForm.comp (innerₗ E) dF.toLinearMap dF.toLinearMap

/-- The second fundamental form for the convention `II(v,w) = -⟪dn(v),dF(w)⟫`. -/
noncomputable def secondFundamentalFormAt (dn dF : V →L[ℝ] E) :
    LinearMap.BilinForm ℝ V :=
  -(LinearMap.BilinForm.comp (innerₗ E) dn.toLinearMap dF.toLinearMap)

/-- A point is umbilic when its second fundamental form is a scalar multiple of its first. -/
def IsUmbilic (V E : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (dF dn : V →L[ℝ] E) : Prop :=
  ∃ κ : ℝ, secondFundamentalFormAt dn dF = κ • firstFundamentalFormAt dF

@[simp]
theorem firstFundamentalFormAt_apply (dF : V →L[ℝ] E) (v w : V) :
    firstFundamentalFormAt dF v w = inner ℝ (dF v) (dF w) :=
  rfl

@[simp]
theorem secondFundamentalFormAt_apply (dn dF : V →L[ℝ] E) (v w : V) :
    secondFundamentalFormAt dn dF v w = -inner ℝ (dn v) (dF w) :=
  rfl

/-- If `dn = c • dF`, the point is umbilic with scalar `-c` under our sign convention. -/
theorem isUmbilic_of_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (c : ℝ) (h : dn = c • dF) :
    IsUmbilic V E dF dn := by
  refine ⟨-c, ?_⟩
  ext v w
  change -inner ℝ (dn v) (dF w) = -c * inner ℝ (dF v) (dF w)
  rw [h, ContinuousLinearMap.smul_apply, real_inner_smul_left, neg_mul]

/-- If `dn` is tangent to the immersion, umbilicity is equivalent to `dn` being a scalar multiple
of `dF`. -/
theorem isUmbilic_iff_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (htangent : dn.range ≤ dF.range) :
    IsUmbilic V E dF dn ↔ ∃ c : ℝ, dn = c • dF := by
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨-κ, ?_⟩
    ext v
    obtain ⟨u, hu⟩ := htangent ⟨v, rfl⟩
    have horth (w : V) : inner ℝ (dn v + κ • dF v) (dF w) = 0 := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ V ↦ B v w) hκ
      change -inner ℝ (dn v) (dF w) = κ * inner ℝ (dF v) (dF w) at h
      rw [inner_add_left, real_inner_smul_left, ← h, add_neg_cancel]
    have hrange : dn v + κ • dF v = dF (u + κ • v) := by
      change dF u = dn v at hu
      rw [map_add, map_smul, ← hu]
    have hzero := horth (u + κ • v)
    rw [← hrange, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hzero
    simpa [ContinuousLinearMap.smul_apply] using
      eq_neg_of_add_eq_zero_left hzero
  · exact fun ⟨c, hc⟩ ↦ isUmbilic_of_normal_deriv_eq_smul dF dn c hc

end EuclideanHypersurface
