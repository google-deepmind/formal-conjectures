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

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

open Metric Set
open scoped Gradient Topology

namespace SphereSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Classical in
/-- The degree-one radial extension of a function on the unit sphere. -/
noncomputable def radialExtension (h : sphere (0 : E) 1 → ℝ) (x : E) : ℝ :=
  if hx : x = 0 then 0
  else ‖x‖ * h ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩

/-- The radial extension restricts to the original function on the unit sphere. -/
@[simp]
theorem radialExtension_coe (h : sphere (0 : E) 1 → ℝ) (p : sphere (0 : E) 1) :
    radialExtension h (p : E) = h p := by
  simp [radialExtension, ne_zero_of_mem_unit_sphere p, norm_eq_of_mem_sphere p]

/-- The radial extension is positively homogeneous of degree one. -/
theorem radialExtension_smul_of_pos (h : sphere (0 : E) 1 → ℝ) (x : E) {t : ℝ}
    (ht : 0 < t) : radialExtension h (t • x) = t * radialExtension h x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hunit (z : E) (hz : z ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
  have hnormalized :
      (⟨‖t • x‖⁻¹ • (t • x), by
        rw [mem_sphere, dist_zero_right]
        exact hunit (t • x) htx⟩ : sphere (0 : E) 1) =
        ⟨‖x‖⁻¹ • x, by
          rw [mem_sphere, dist_zero_right]
          exact hunit x hx⟩ := by
    apply Subtype.ext
    simp only [hnorm, smul_smul]
    congr 1
    field_simp [ht.ne']
  simp only [radialExtension, dif_neg htx, dif_neg hx]
  rw [hnormalized, hnorm]
  ring

/-- The contact map associated to a differentiable positively homogeneous function on the
ambient vector space. -/
noncomputable def homogeneousGradient [CompleteSpace E]
    (H : E → ℝ) (p : sphere (0 : E) 1) : E :=
  ∇ H (p : E)

/-- Euler's identity for a differentiable function that is positively homogeneous of degree
one. This is the contact identity underlying the support-gradient construction. -/
theorem inner_homogeneousGradient [CompleteSpace E] (H : E → ℝ) (p : sphere (0 : E) 1)
    (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) (p : E) = H p := by
  rw [homogeneousGradient, inner_gradient_left hH]
  have hline : HasDerivAt (fun t : ℝ ↦ H ((p : E) + t • (p : E)))
      (fderiv ℝ H (p : E) (p : E)) 0 := by
    have harg : HasDerivAt (fun t : ℝ ↦ (p : E) + t • (p : E)) (p : E) 0 :=
      by
        simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using
          (hasDerivAt_const (x := (0 : ℝ)) (p : E)).add
            ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (p : E))
    simpa [Function.comp_def] using
      hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
  have heq : (fun t : ℝ ↦ H ((p : E) + t • (p : E))) =ᶠ[𝓝 0]
      fun t : ℝ ↦ (1 + t) * H p := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    calc
      H ((p : E) + t • (p : E)) = H ((1 + t) • (p : E)) := by rw [add_smul, one_smul]
      _ = (1 + t) * H p := hhom (1 + t) (by linarith [(abs_lt.mp ht).1])
  have hright : HasDerivAt (fun t : ℝ ↦ (1 + t) * H p) (H p) 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1 |>.mul_const (H p) using 1
    all_goals ring
  exact (hline.congr_of_eventuallyEq heq.symm).unique hright

/-- A differentiable positively homogeneous majorant has a unique contact point: its gradient.
This is the ambient form of the first-variation argument for support functions. -/
theorem eq_homogeneousGradient_of_global_support [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (x : E) (hH : DifferentiableAt ℝ H (p : E))
    (hmajor : ∀ y : E, inner ℝ x y ≤ H y) (hcontact : inner ℝ x (p : E) = H p) :
    x = homogeneousGradient H p := by
  let G : E → ℝ := fun y ↦ H y - inner ℝ x y
  have hmin : IsMinOn G univ (p : E) := by
    intro y _
    dsimp [G]
    rw [hcontact]
    linarith [hmajor y]
  have hlinear : DifferentiableAt ℝ (fun y : E ↦ inner ℝ x y) (p : E) :=
    (innerSL ℝ x).differentiableAt
  have hderiv : fderiv ℝ H (p : E) = innerSL ℝ x := by
    have hzero := (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
    have hinner_deriv :
        fderiv ℝ (fun y : E ↦ inner ℝ x y) (p : E) = innerSL ℝ x := by
      simpa only [innerSL_apply_apply] using (innerSL ℝ x).hasFDerivAt.fderiv
    rw [show G = fun y : E ↦ H y - inner ℝ x y by rfl,
      fderiv_fun_sub hH hlinear, hinner_deriv] at hzero
    exact sub_eq_zero.mp hzero
  apply ext_inner_right ℝ
  intro y
  rw [homogeneousGradient, inner_gradient_left hH, hderiv, innerSL_apply_apply]

/-- The gradient of a differentiable convex function that is positively homogeneous of degree
one lies below that function in every direction. -/
theorem inner_homogeneousGradient_le [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (y : E)
    (hconvex : ConvexOn ℝ univ H) (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) y ≤ H y := by
  let e : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (p : E) y
  have hline_convex : ConvexOn ℝ univ (H ∘ e) := by
    simpa [e] using hconvex.comp_affineMap e
  have he0 : e 0 = (p : E) := by simp [e]
  have he1 : e 1 = y := by simp [e]
  have he_deriv : HasDerivAt e (y - (p : E)) (0 : ℝ) := by
    simpa [e] using (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ) (E := E)
      (a := (p : E)) (b := y) (x := (0 : ℝ)))
  have hline_deriv : HasDerivAt (H ∘ e) (fderiv ℝ H (p : E) (y - (p : E))) 0 := by
    exact hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) he_deriv he0.symm
  have hslope := hline_convex.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hline_deriv
  have heuler : fderiv ℝ H (p : E) (p : E) = H p := by
    rw [← inner_homogeneousGradient H p hH hhom, homogeneousGradient,
      inner_gradient_left hH]
  have hslope' : fderiv ℝ H (p : E) (y - (p : E)) ≤ H y - H p := by
    simpa [slope, Function.comp_apply, he0, he1] using hslope
  rw [map_sub, heuler] at hslope'
  rw [homogeneousGradient, inner_gradient_left hH]
  linarith

/-- Stereographic charts based at antipodal unit vectors are related by radial inversion. -/
theorem stereoToFun_stereoInvFunAux_neg {v w : E} (hv : ‖v‖ = 1)
    (hw : w ∈ (ℝ ∙ v)ᗮ) (hw0 : w ≠ 0) :
    stereoToFun v (stereoInvFunAux (-v) w) =
      (4 / ‖w‖ ^ 2) • (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) := by
  rw [stereoToFun_apply, stereoInvFunAux_apply]
  have hprojw : (ℝ ∙ v)ᗮ.orthogonalProjection w = ⟨w, hw⟩ := by
    simpa using (ℝ ∙ v)ᗮ.orthogonalProjection_mem_subspace_eq_self
      (⟨w, hw⟩ : (ℝ ∙ v)ᗮ)
  have hprojneg : (ℝ ∙ v)ᗮ.orthogonalProjection (-v) = 0 := by
    rw [map_neg, Submodule.orthogonalProjection_orthogonalComplement_singleton_eq_zero]
    exact neg_zero
  have hinnerw : inner ℝ v w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hinnerv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  simp only [map_smul, map_add, hprojw, hprojneg, smul_zero, add_zero, innerSL_apply_apply,
    hinnerw, hinnerv, inner_neg_right, smul_smul]
  have hwsub : (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) ≠ 0 := by
    intro h
    exact hw0 (congr_arg Subtype.val h)
  rw [smul_left_inj hwsub]
  simp only [smul_eq_mul]
  have hdenom :
      1 - (‖w‖ ^ 2 + 4)⁻¹ * ((‖w‖ ^ 2 - 4) * -1) =
        2 * ‖w‖ ^ 2 / (‖w‖ ^ 2 + 4) := by
    field_simp
    ring
  simp only [zero_add]
  rw [hdenom]
  field_simp [norm_ne_zero_iff.mpr hw0]

/-- The closed convex set cut out by the supporting half-spaces prescribed by `h`. -/
def body (h : sphere (0 : E) 1 → ℝ) : Set E :=
  {x | ∀ p : sphere (0 : E) 1, inner ℝ (p : E) x ≤ h p}

/-- A support-function body is convex. -/
theorem body_convex (h : sphere (0 : E) 1 → ℝ) : Convex ℝ (body h) := by
  rw [body, setOf_forall]
  exact convex_iInter fun p ↦
    convex_halfSpace_le (innerSL ℝ (p : E)).toLinearMap.isLinear (h p)

/-- A support-function body is closed. -/
theorem body_isClosed (h : sphere (0 : E) 1 → ℝ) : IsClosed (body h) := by
  rw [body, setOf_forall]
  exact isClosed_iInter fun p ↦ isClosed_Iic.preimage (innerSL ℝ (p : E)).continuous

/-- If `h` is bounded below by a positive constant, its support-function body has nonempty
interior. -/
theorem body_interior_nonempty (h : sphere (0 : E) 1 → ℝ) {r : ℝ} (hr : 0 < r)
    (hlower : ∀ p, r ≤ h p) : (interior (body h)).Nonempty := by
  have hball : ball (0 : E) r ⊆ body h := by
    intro x hx p
    calc
      inner ℝ (p : E) x ≤ ‖(p : E)‖ * ‖x‖ := real_inner_le_norm _ _
      _ = ‖x‖ := by rw [norm_eq_of_mem_sphere p, one_mul]
      _ ≤ r := (by simpa [mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
      _ ≤ h p := hlower p
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (ball_mem_nhds 0 hr) hball

/-- A uniform upper bound on `h` bounds its support-function body. -/
theorem body_isBounded (h : sphere (0 : E) 1 → ℝ) {R : ℝ} (hupper : ∀ p, h p ≤ R) :
    Bornology.IsBounded (body h) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
  refine ⟨max R 0, ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    let p : sphere (0 : E) 1 := ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, hxnorm]⟩
    have hp : inner ℝ (p : E) x ≤ h p := hx p
    have hinner : inner ℝ (p : E) x = ‖x‖ := by
      change inner ℝ (‖x‖⁻¹ • x) x = ‖x‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      calc
        ‖x‖⁻¹ * (‖x‖ * ‖x‖) = (‖x‖⁻¹ * ‖x‖) * ‖x‖ := by ring
        _ = ‖x‖ := by rw [inv_mul_cancel₀ hxnorm, one_mul]
    rw [hinner] at hp
    exact (hp.trans (hupper p)).trans (le_max_left _ _)

/-- In a proper real inner-product space, a uniformly upper-bounded support function cuts out a
compact body. -/
theorem body_isCompact [ProperSpace E] (h : sphere (0 : E) 1 → ℝ) {R : ℝ}
    (hupper : ∀ p, h p ≤ R) : IsCompact (body h) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨body_isClosed h, body_isBounded h hupper⟩

/-- A continuous function on the unit sphere cuts out a compact support-function body. -/
theorem body_isCompact_of_continuous [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (hh : Continuous h) : IsCompact (body h) := by
  obtain ⟨R, hR⟩ := (isCompact_range hh).bddAbove
  exact body_isCompact h fun p ↦ hR ⟨p, rfl⟩

/-- Every boundary point of a closed convex body with nonempty interior admits an outward unit
supporting normal. -/
theorem exists_unit_supporting_normal {K : Set E} (hconvex : Convex ℝ K)
    [CompleteSpace E] (hclosed : IsClosed K) (hinterior : (interior K).Nonempty) {x : E}
    (hx : x ∈ frontier K) :
    ∃ p : sphere (0 : E) 1, ∀ y ∈ K, inner ℝ (p : E) y ≤ inner ℝ (p : E) x := by
  have hx_not_interior : x ∉ interior K := by
    rw [frontier] at hx
    exact hx.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconvex.interior isOpen_interior
    hx_not_interior
  have hf0 : f ≠ 0 := by
    intro hzero
    obtain ⟨y, hy⟩ := hinterior
    simpa [hzero] using hf y hy
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hv0 : v ≠ 0 := (InnerProductSpace.toDual ℝ E).symm.map_ne_zero_iff.mpr hf0
  let p : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
    simp [norm_smul, hv0]⟩
  refine ⟨p, fun y hy ↦ ?_⟩
  have hhalf_closed : IsClosed {z : E | f z ≤ f x} :=
    isClosed_Iic.preimage f.continuous
  have hhalf : closure (interior K) ⊆ {z : E | f z ≤ f x} :=
    closure_minimal (fun z hz ↦ (hf z hz).le) hhalf_closed
  have hclosure : closure (interior K) = K := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior,
      hclosed.closure_eq]
  have hfy : f y ≤ f x := hhalf (hclosure.symm ▸ hy)
  change inner ℝ (‖v‖⁻¹ • v) y ≤ inner ℝ (‖v‖⁻¹ • v) x
  simpa only [real_inner_smul_left, v, InnerProductSpace.toDual_symm_apply] using
    mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr (norm_nonneg v))

/-- Pointwise contact and cross-support inequalities place every parametrized point in the
support-function body and make it attain the corresponding supporting hyperplane. -/
theorem contact_mem_body (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ body h ∧ inner ℝ (F p) (p : E) = h p ∧
      ∀ x ∈ body h, inner ℝ x (p : E) ≤ h p := by
  intro p
  refine ⟨fun q ↦ ?_, hcontact p, fun x hx ↦ ?_⟩
  · simpa [real_inner_comm] using hcross p q
  · simpa [real_inner_comm] using hx p

/-- A parametrized contact point lies on the frontier of the support-function body. -/
theorem contact_mem_frontier (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ frontier (body h) := by
  intro p
  rw [frontier, (body_isClosed h).closure_eq]
  refine ⟨(contact_mem_body h F hcontact hcross p).1, ?_⟩
  intro hpinterior
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hpinterior) with
    ⟨ε, hε, hball⟩
  let y := F p + (ε / 2) • (p : E)
  have hyball : y ∈ ball (F p) ε := by
    rw [mem_ball, dist_eq_norm]
    simp [y, norm_smul, norm_eq_of_mem_sphere p]
    rw [abs_of_pos hε]
    linarith
  have hybody : y ∈ body h := hball hyball
  have hy_support := hybody p
  have hpp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
    norm_num
  have hcontact' : inner ℝ (p : E) (F p) = h p := by
    rw [real_inner_comm]
    exact hcontact p
  have hy_inner : inner ℝ (p : E) y = h p + ε / 2 := by
    rw [show y = F p + (ε / 2) • (p : E) by rfl, inner_add_right,
      hcontact', real_inner_smul_right, hpp, mul_one]
  rw [hy_inner] at hy_support
  linarith

/-- If every exposed contact face is the prescribed singleton, the contact parametrization covers
the whole frontier of its support-function body. -/
theorem range_eq_frontier_of_unique_contact [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hunique : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → x = F p) :
    range F = frontier (body h) := by
  apply Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    exact contact_mem_frontier h F hcontact hcross p
  · intro x hx
    obtain ⟨p, hp⟩ := exists_unit_supporting_normal (body_convex h) (body_isClosed h)
      hinterior hx
    have hxbody : x ∈ body h := by
      rw [frontier, (body_isClosed h).closure_eq] at hx
      exact hx.1
    have hFpbody := (contact_mem_body h F hcontact hcross p).1
    have hle : h p ≤ inner ℝ (p : E) x := by
      rw [← hcontact p, real_inner_comm]
      exact hp (F p) hFpbody
    have hxeq : inner ℝ (p : E) x = h p :=
      le_antisymm (hxbody p) hle
    exact ⟨p, (hunique p x hxbody hxeq).symm⟩

/-- A contact point is uniquely determined once its displacement from the prescribed point is
orthogonal to every tangent vector. This is the linear-algebra step in the first-variation
argument for support parametrizations. -/
theorem eq_contact_of_tangent_orthogonal (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    {p : sphere (0 : E) 1} {x : E} (hxeq : inner ℝ (p : E) x = h p)
    (htangent : ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ → inner ℝ (x - F p) v = 0) :
    x = F p := by
  have hdisplacement : x - F p ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, hxeq]
    have hpcontact : inner ℝ (p : E) (F p) = h p := by
      rw [real_inner_comm]
      exact hcontact p
    rw [hpcontact, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp
    (htangent (x - F p) hdisplacement))

/-- First variation at every exposed contact point, together with contact and cross-support,
forces a parametrization to cover the whole frontier. -/
theorem range_eq_frontier_of_first_variation [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    range F = frontier (body h) :=
  range_eq_frontier_of_unique_contact h F hcontact hcross hinterior fun p x hx hxeq ↦
    eq_contact_of_tangent_orthogonal h F hcontact hxeq (hstationary p x hx hxeq)

/-- Contact, cross-support, and first variation produce the compact convex body represented by a
support function. This packages the set-theoretic part of the support-gradient construction. -/
theorem exists_compact_body_of_first_variation [ProperSpace E] [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hh : Continuous h) {r : ℝ} (hr : 0 < r) (hlower : ∀ p, r ≤ h p)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    ∃ K : Set E, Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      range F = frontier K ∧ ∀ p, F p ∈ K ∧ inner ℝ (F p) (p : E) = h p ∧
        ∀ x ∈ K, inner ℝ x (p : E) ≤ h p := by
  refine ⟨body h, body_convex h, body_isCompact_of_continuous h hh,
    body_interior_nonempty h hr hlower,
    range_eq_frontier_of_first_variation h F hcontact hcross
      (body_interior_nonempty h hr hlower) hstationary, ?_⟩
  exact contact_mem_body h F hcontact hcross

/-- Strict cross-support separates the parametrizing normals, so the contact map is injective. -/
theorem injective_of_strictCross (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Function.Injective F := by
  intro p q hpq
  by_contra hpne
  have hpq_strict := hstrict p q hpne
  rw [hpq, hcontact q] at hpq_strict
  exact (lt_irrefl _ hpq_strict)

/-- A continuous strict contact parametrization of the unit sphere is a topological embedding. -/
theorem isEmbedding_of_strictCross [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E) (hF : Continuous F)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Topology.IsEmbedding F :=
  (hF.isClosedEmbedding (injective_of_strictCross h F hcontact hstrict)).isEmbedding

end SphereSupport
