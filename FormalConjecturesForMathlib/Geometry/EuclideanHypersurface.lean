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

@[expose] public section

/-!
# Extrinsic fundamental forms in Euclidean space

This small API packages the first and second fundamental forms determined by the differential of
an immersion and a chosen normal field. The sign in the second form is the convention
`II(v, w) = -⟪dn(v), dF(w)⟫`; consequently `dn = c • dF` corresponds to `II = (-c) • I`.
-/

open scoped RealInnerProductSpace

namespace EuclideanHypersurface

variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first fundamental form induced by `dF`. -/
noncomputable def firstFundamentalFormAt (dF : V →L[ℝ] E) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w ↦ inner ℝ (dF v) (dF w))
    (by simp [inner_add_left]) (by simp [real_inner_smul_left])
    (by simp [inner_add_right]) (by simp [real_inner_smul_right])

/-- The second fundamental form for the convention `II(v,w) = -⟪dn(v),dF(w)⟫`. -/
noncomputable def secondFundamentalFormAt (dn dF : V →L[ℝ] E) :
    LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w ↦ -inner ℝ (dn v) (dF w))
    (by simp [inner_add_left, add_comm]) (by simp [real_inner_smul_left])
    (by simp [inner_add_right, add_comm]) (by simp [real_inner_smul_right])

/-- A point is umbilic when its second fundamental form is a scalar multiple of its first. -/
def IsUmbilicByFundamentalForms (dF dn : V →L[ℝ] E) : Prop :=
  ∃ κ : ℝ, secondFundamentalFormAt dn dF = κ • firstFundamentalFormAt dF

@[simp]
theorem firstFundamentalFormAt_apply (dF : V →L[ℝ] E) (v w : V) :
    firstFundamentalFormAt dF v w = inner ℝ (dF v) (dF w) := by
  rfl

@[simp]
theorem secondFundamentalFormAt_apply (dn dF : V →L[ℝ] E) (v w : V) :
    secondFundamentalFormAt dn dF v w = -inner ℝ (dn v) (dF w) := by
  rfl

/-- A scalar normal differential gives the corresponding scalar second fundamental form.

The minus sign is forced by `secondFundamentalFormAt`'s shape-operator convention. -/
theorem isUmbilicByFundamentalForms_of_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (c : ℝ) (h : dn = c • dF) :
    IsUmbilicByFundamentalForms dF dn := by
  refine ⟨-c, ?_⟩
  ext v w
  change -inner ℝ (dn v) (dF w) = -c * inner ℝ (dF v) (dF w)
  rw [h, ContinuousLinearMap.smul_apply, real_inner_smul_left]
  ring

/-- Under tangency hypotheses, the fundamental-form and scalar-normal-differential definitions
of an umbilic are equivalent. The range hypothesis is exactly what rules out an undetected
normal component of `dn`. -/
theorem isUmbilicByFundamentalForms_iff_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (htangent : dn.range ≤ dF.range) :
    IsUmbilicByFundamentalForms dF dn ↔ ∃ c : ℝ, dn = c • dF := by
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨-κ, ?_⟩
    ext v
    obtain ⟨u, hu⟩ := htangent ⟨v, rfl⟩
    have horth (w : V) : inner ℝ (dn v + κ • dF v) (dF w) = 0 := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ V ↦ B v w) hκ
      change -inner ℝ (dn v) (dF w) = κ * inner ℝ (dF v) (dF w) at h
      rw [inner_add_left, real_inner_smul_left]
      linarith [h]
    have hrange : dn v + κ • dF v = dF (u + κ • v) := by
      change dF u = dn v at hu
      rw [map_add, map_smul, ← hu]
    have := horth (u + κ • v)
    rw [← hrange, real_inner_self_eq_norm_sq] at this
    have hzero : dn v + κ • dF v = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (dn v + κ • dF v)]
    simpa only [ContinuousLinearMap.smul_apply, neg_smul] using
      eq_neg_of_add_eq_zero_left hzero
  · rintro ⟨c, hc⟩
    exact isUmbilicByFundamentalForms_of_normal_deriv_eq_smul dF dn c hc

end EuclideanHypersurface
