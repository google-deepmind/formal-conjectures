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

import RestrictedWeilCriterionResidueCoefficientV11
import RestrictedWeilCriterionPoleIsolationV10
import MeromorphicIdentityPreconnectedV11
import RHZeroKernelLaplaceAnalyticV12
import WeilRHImpliesFinalSignV11
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

open Set Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.V13Scratch

open AEGIS.RHFinalClosureV1
open AEGIS.RHMillenniumGateV10
open AEGIS.RestrictedWeilCriterionLaplaceV10
open AEGIS.RestrictedWeilCriterionPoleIsolationV10
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.MeromorphicIdentityPreconnectedV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.WeilZeroTwoPointV11
open AEGIS.RestrictedWeilCriterionZeroKernelV10
open scoped Classical

theorem zero_coefficient_v10_eq_v11
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ZeroCoefficientV10 g rho = WeilZeroCoefficientV11 g rho := by
  rfl

theorem centered_exponent_v12_eq_neg_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilCenteredZeroExponentV12 rho =
      - CenteredZeroExponentV10 rho := by
  unfold WeilCenteredZeroExponentV12 CenteredZeroExponentV10
  ring

theorem centered_zero_dist_ge_isolation_v12
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        sigma ≠ rho →
        eps ≤
          dist (WeilCenteredZeroExponentV12 sigma)
            (WeilCenteredZeroExponentV12 rho) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v10 rho
  refine ⟨eps, heps, ?_⟩
  intro sigma hne
  have h := hsep sigma hne
  simpa [centered_exponent_v12_eq_neg_v10] using h

def RightHalfPlaneV13 : Set ℂ := {w : ℂ | 0 < w.re}

theorem rightHalfPlane_isPreconnected_v13 :
    IsPreconnected RightHalfPlaneV13 := by
  simpa [RightHalfPlaneV13] using
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected

theorem final_sign_to_universal_zero_quadratic_v13
    (h : FinalSignResidualV1) :
    UniversalZeroQuadraticNonnegativeV10 :=
  universal_zero_quadratic_iff_final_sign_v10.mpr h

def ZeroResolventRemainderV13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (w : ℂ) : ℂ :=
  ∑' sigma : RiemannNontrivialZeroIndexV2,
    if sigma = rho then 0 else
      WeilZeroCoefficientV11 g sigma /
        (w - WeilCenteredZeroExponentV12 sigma)

private theorem other_center_denominator_lower_v12
    (rho sigma : RiemannNontrivialZeroIndexV2)
    (eps : ℝ)
    (hsep : ∀ tau : RiemannNontrivialZeroIndexV2,
      tau ≠ rho →
      eps ≤ dist (WeilCenteredZeroExponentV12 tau)
        (WeilCenteredZeroExponentV12 rho))
    (hsigma : sigma ≠ rho)
    {w : ℂ}
    (hw : w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) :
    eps / 2 < dist w (WeilCenteredZeroExponentV12 sigma) := by
  have hs := hsep sigma hsigma
  have ht := dist_triangle
    (WeilCenteredZeroExponentV12 sigma) w
    (WeilCenteredZeroExponentV12 rho)
  have hw' :
      dist w (WeilCenteredZeroExponentV12 rho) < eps / 2 := by
    simpa [Metric.mem_ball] using hw
  rw [dist_comm (WeilCenteredZeroExponentV12 sigma) w] at ht
  linarith

theorem zero_resolvent_remainder_differentiable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      DifferentiableOn ℂ (ZeroResolventRemainderV13 g rho)
        (Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v12 rho
  have hr : 0 < eps / 2 := by linarith
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))

  have hterm :
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        DifferentiableOn ℂ
          (fun w : ℂ =>
            if sigma = rho then 0 else
              WeilZeroCoefficientV11 g sigma /
                (w - WeilCenteredZeroExponentV12 sigma))
          (Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) := by
    intro sigma
    by_cases hsigma : sigma = rho
    · simp [hsigma]
    · intro w hw
      have hd :=
        other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
      have hne :
          w - WeilCenteredZeroExponentV12 sigma ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        rw [heq, dist_self] at hd
        linarith
      simp only [hsigma, if_false]
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := exact hne)

  have hbound :
      ∀ (sigma : RiemannNontrivialZeroIndexV2) (w : ℂ),
        w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2) →
        ‖(if sigma = rho then 0 else
          WeilZeroCoefficientV11 g sigma /
            (w - WeilCenteredZeroExponentV12 sigma))‖ ≤ u sigma := by
    intro sigma w hw
    by_cases hsigma : sigma = rho
    · simp [hsigma, u]
      positivity
    · simp only [hsigma, if_false]
      have hd :=
        other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
      have hden :
          eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
        simpa [dist_eq_norm] using le_of_lt hd
      have hrec :
          1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤
            1 / (eps / 2) :=
        one_div_le_one_div_of_le hr hden
      rw [norm_div]
      dsimp [u]
      simpa [div_eq_mul_inv, one_div] using
        mul_le_mul_of_nonneg_left hrec
          (norm_nonneg (WeilZeroCoefficientV11 g sigma))

  have hd :=
    differentiableOn_tsum_of_summable_norm
      (F := fun sigma w =>
        if sigma = rho then 0 else
          WeilZeroCoefficientV11 g sigma /
            (w - WeilCenteredZeroExponentV12 sigma))
      hu hterm Metric.isOpen_ball hbound

  refine ⟨eps, heps, ?_⟩
  unfold ZeroResolventRemainderV13
  exact hd

private theorem zero_resolvent_remainder_summable_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (eps : ℝ) (heps : 0 < eps)
    (hsep : ∀ sigma : RiemannNontrivialZeroIndexV2,
      sigma ≠ rho →
      eps ≤ dist (WeilCenteredZeroExponentV12 sigma)
        (WeilCenteredZeroExponentV12 rho))
    {w : ℂ}
    (hw : w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2)) :
    Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
      if sigma = rho then 0 else
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)) := by
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hr : 0 < eps / 2 := by linarith
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))
  apply Summable.of_norm_bounded hu
  intro sigma
  by_cases hsigma : sigma = rho
  · simp [hsigma, u]
    positivity
  · simp only [hsigma, if_false]
    have hd :=
      other_center_denominator_lower_v12 rho sigma eps hsep hsigma hw
    have hden :
        eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
      simpa [dist_eq_norm] using le_of_lt hd
    have hrec :
        1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤ 1 / (eps / 2) :=
      one_div_le_one_div_of_le hr hden
    rw [norm_div]
    dsimp [u]
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hrec
        (norm_nonneg (WeilZeroCoefficientV11 g sigma))

theorem zero_resolvent_split_near_pole_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ w ∈ Metric.ball (WeilCenteredZeroExponentV12 rho) (eps / 2),
        WeilZeroResolventV12 g w =
          WeilZeroCoefficientV11 g rho /
            (w - WeilCenteredZeroExponentV12 rho) +
          ZeroResolventRemainderV13 g rho w := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_isolation_v12 rho
  refine ⟨eps, heps, ?_⟩
  intro w hw
  have hrem :=
    zero_resolvent_remainder_summable_near_pole_v13
      g rho eps heps hsep hw
  have hfull :
      Summable (fun sigma : RiemannNontrivialZeroIndexV2 =>
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)) := by
    apply hrem.congr_cofinite
    filter_upwards [eventually_cofinite_ne rho] with sigma hsigma
    simp [hsigma]
  unfold WeilZeroResolventV12 ZeroResolventRemainderV13
  exact hfull.tsum_eq_add_tsum_ite rho


theorem zero_resolvent_order_eq_neg_one_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2)
    (hcoef : WeilZeroCoefficientV11 g rho ≠ 0) :
    meromorphicOrderAt (WeilZeroResolventV12 g)
      (WeilCenteredZeroExponentV12 rho) = (-1 : ℤ) := by
  let y : ℂ := WeilCenteredZeroExponentV12 rho

  obtain ⟨epsR, hepsR, hRdiff⟩ :=
    zero_resolvent_remainder_differentiable_near_pole_v13 g rho
  have hRanalytic :
      AnalyticAt ℂ (ZeroResolventRemainderV13 g rho) y := by
    apply hRdiff.analyticAt
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsR / 2))

  let G : ℂ → ℂ := fun z =>
    WeilZeroCoefficientV11 g rho +
      (z - y) * ZeroResolventRemainderV13 g rho z

  have hGanalytic : AnalyticAt ℂ G y := by
    dsimp [G]
    exact analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul hRanalytic)

  have hGne : G y ≠ 0 := by
    simpa [G] using hcoef

  obtain ⟨epsS, hepsS, hsplit⟩ :=
    zero_resolvent_split_near_pole_v13 g rho

  have hball :
      Metric.ball y (epsS / 2) ∈ 𝓝 y := by
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsS / 2))

  have hballNE :
      ∀ᶠ z in 𝓝[≠] y, z ∈ Metric.ball y (epsS / 2) :=
    mem_nhdsWithin_of_mem_nhds hball

  have heq :
      ∀ᶠ z in 𝓝[≠] y,
        WeilZeroResolventV12 g z =
          (z - y) ^ (-1 : ℤ) * G z := by
    filter_upwards [hballNE, self_mem_nhdsWithin] with z hzball hzNE
    have hzy : z - y ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa using hzNE
    have hs :=
      hsplit z (by simpa [y] using hzball)
    rw [hs]
    dsimp [G]
    rw [zpow_neg_one]
    have hzy' : z - WeilCenteredZeroExponentV12 rho ≠ 0 := hzy
    field_simp [hzy, hzy']
    ring

  have hmer :
      MeromorphicAt (WeilZeroResolventV12 g) y := by
    rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
    refine ⟨(-1 : ℤ), G, hGanalytic, ?_⟩
    filter_upwards [heq] with z hz
    simpa [smul_eq_mul] using hz

  rw [meromorphicOrderAt_eq_int_iff hmer]
  refine ⟨G, hGanalytic, hGne, ?_⟩
  filter_upwards [heq] with z hz
  simpa [smul_eq_mul] using hz


private theorem zeta_shift_ne_zero_of_not_center_v13
    {w : ℂ} (hw : 0 < w.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w) :
    riemannZeta (w + (1 / 2 : ℂ)) ≠ 0 := by
  intro hz
  let s : ℂ := w + (1 / 2 : ℂ)
  have hspos : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have htriv :
      ¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hspos
    have hnonpos :
        (-(2 : ℂ) * ((n : ℂ) + 1)).re ≤ 0 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp
      linarith
    exact (not_lt_of_ge hnonpos) hspos
  let rho : RiemannNontrivialZeroIndexV2 :=
    ⟨s, hz, htriv⟩
  have hc : WeilCenteredZeroExponentV12 rho = w := by
    dsimp [rho, s, WeilCenteredZeroExponentV12]
    ring
  exact hnopole rho hc

private theorem centered_zero_dist_ge_of_not_center_v13
    {w : ℂ} (hw : 0 < w.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        eps ≤ dist (WeilCenteredZeroExponentV12 sigma) w := by
  let s : ℂ := w + (1 / 2 : ℂ)
  have hz : riemannZeta s ≠ 0 := by
    simpa [s] using zeta_shift_ne_zero_of_not_center_v13 hw hnopole
  have hscompl : s ∈ riemannZetaZerosᶜ := by
    simpa [mem_riemannZetaZeros] using hz
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.mp isClosed_riemannZetaZeros.isOpen_compl s hscompl
  refine ⟨eps, heps, ?_⟩
  intro sigma
  by_contra hnot
  have hlt :
      dist (WeilCenteredZeroExponentV12 sigma) w < eps :=
    lt_of_not_ge hnot
  have hdist :
      dist sigma.1 s =
        dist (WeilCenteredZeroExponentV12 sigma) w := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    dsimp [s, WeilCenteredZeroExponentV12]
    ring
  have hsball : sigma.1 ∈ Metric.ball s eps := by
    rw [Metric.mem_ball, hdist]
    exact hlt
  have hsnotzero : sigma.1 ∉ riemannZetaZeros :=
    hball hsball
  exact hsnotzero (mem_riemannZetaZeros.mpr sigma.2.1)

private theorem center_denominator_lower_from_point_v13
    (w0 : ℂ)
    (sigma : RiemannNontrivialZeroIndexV2)
    (eps : ℝ)
    (hsep : ∀ tau : RiemannNontrivialZeroIndexV2,
      eps ≤ dist (WeilCenteredZeroExponentV12 tau) w0)
    {w : ℂ} (hw : w ∈ Metric.ball w0 (eps / 2)) :
    eps / 2 < dist w (WeilCenteredZeroExponentV12 sigma) := by
  have hs := hsep sigma
  have ht :=
    dist_triangle (WeilCenteredZeroExponentV12 sigma) w w0
  have hw' : dist w w0 < eps / 2 := by
    simpa [Metric.mem_ball] using hw
  rw [dist_comm (WeilCenteredZeroExponentV12 sigma) w] at ht
  linarith

private theorem zero_resolvent_differentiable_near_nonpole_v13
    (g : WeilCompactSmoothGV1)
    {w0 : ℂ} (hw0 : 0 < w0.re)
    (hnopole : ∀ rho : RiemannNontrivialZeroIndexV2,
      WeilCenteredZeroExponentV12 rho ≠ w0) :
    ∃ eps : ℝ, 0 < eps ∧
      DifferentiableOn ℂ (WeilZeroResolventV12 g)
        (Metric.ball w0 (eps / 2)) := by
  obtain ⟨eps, heps, hsep⟩ :=
    centered_zero_dist_ge_of_not_center_v13 hw0 hnopole
  have hr : 0 < eps / 2 := by linarith
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun sigma =>
    ‖WeilZeroCoefficientV11 g sigma‖ * (1 / (eps / 2))
  have hu : Summable u := by
    dsimp [u]
    exact (zero_coefficient_norm_summable_v12 g).mul_right (1 / (eps / 2))

  have hterm :
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        DifferentiableOn ℂ
          (fun w : ℂ =>
            WeilZeroCoefficientV11 g sigma /
              (w - WeilCenteredZeroExponentV12 sigma))
          (Metric.ball w0 (eps / 2)) := by
    intro sigma w hw
    have hd :=
      center_denominator_lower_from_point_v13 w0 sigma eps hsep hw
    have hne :
        w - WeilCenteredZeroExponentV12 sigma ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      rw [heq, dist_self] at hd
      linarith
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hne)

  have hbound :
      ∀ (sigma : RiemannNontrivialZeroIndexV2) (w : ℂ),
        w ∈ Metric.ball w0 (eps / 2) →
        ‖WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma)‖ ≤ u sigma := by
    intro sigma w hw
    have hd :=
      center_denominator_lower_from_point_v13 w0 sigma eps hsep hw
    have hden :
        eps / 2 ≤ ‖w - WeilCenteredZeroExponentV12 sigma‖ := by
      simpa [dist_eq_norm] using le_of_lt hd
    have hrec :
        1 / ‖w - WeilCenteredZeroExponentV12 sigma‖ ≤
          1 / (eps / 2) :=
      one_div_le_one_div_of_le hr hden
    rw [norm_div]
    dsimp [u]
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hrec
        (norm_nonneg (WeilZeroCoefficientV11 g sigma))

  have hd :=
    differentiableOn_tsum_of_summable_norm
      (F := fun sigma w =>
        WeilZeroCoefficientV11 g sigma /
          (w - WeilCenteredZeroExponentV12 sigma))
      hu hterm Metric.isOpen_ball hbound

  refine ⟨eps, heps, ?_⟩
  unfold WeilZeroResolventV12
  exact hd

theorem zero_resolvent_meromorphicAt_center_v13
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    MeromorphicAt (WeilZeroResolventV12 g)
      (WeilCenteredZeroExponentV12 rho) := by
  let y : ℂ := WeilCenteredZeroExponentV12 rho
  obtain ⟨epsR, hepsR, hRdiff⟩ :=
    zero_resolvent_remainder_differentiable_near_pole_v13 g rho
  have hRanalytic :
      AnalyticAt ℂ (ZeroResolventRemainderV13 g rho) y := by
    apply hRdiff.analyticAt
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsR / 2))
  let G : ℂ → ℂ := fun z =>
    WeilZeroCoefficientV11 g rho +
      (z - y) * ZeroResolventRemainderV13 g rho z
  have hGanalytic : AnalyticAt ℂ G y := by
    dsimp [G]
    exact analyticAt_const.add
      ((analyticAt_id.sub analyticAt_const).mul hRanalytic)
  obtain ⟨epsS, hepsS, hsplit⟩ :=
    zero_resolvent_split_near_pole_v13 g rho
  have hball :
      Metric.ball y (epsS / 2) ∈ 𝓝 y := by
    simpa [y] using
      (Metric.ball_mem_nhds
        (WeilCenteredZeroExponentV12 rho) (by linarith : 0 < epsS / 2))
  have hballNE :
      ∀ᶠ z in 𝓝[≠] y, z ∈ Metric.ball y (epsS / 2) :=
    mem_nhdsWithin_of_mem_nhds hball
  have heq :
      ∀ᶠ z in 𝓝[≠] y,
        WeilZeroResolventV12 g z =
          (z - y) ^ (-1 : ℤ) * G z := by
    filter_upwards [hballNE, self_mem_nhdsWithin] with z hzball hzNE
    have hzy : z - y ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa using hzNE
    have hs := hsplit z (by simpa [y] using hzball)
    rw [hs]
    dsimp [G]
    rw [zpow_neg_one]
    have hzy' : z - WeilCenteredZeroExponentV12 rho ≠ 0 := hzy
    field_simp [hzy, hzy']
    ring
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨(-1 : ℤ), G, hGanalytic, ?_⟩
  filter_upwards [heq] with z hz
  simpa [smul_eq_mul] using hz

theorem zero_resolvent_meromorphicOn_rightHalfPlane_v13
    (g : WeilCompactSmoothGV1) :
    MeromorphicOn (WeilZeroResolventV12 g) RightHalfPlaneV13 := by
  intro w hw
  by_cases hpole :
      ∃ rho : RiemannNontrivialZeroIndexV2,
        WeilCenteredZeroExponentV12 rho = w
  · obtain ⟨rho, hrho⟩ := hpole
    rw [← hrho]
    exact zero_resolvent_meromorphicAt_center_v13 g rho
  · push_neg at hpole
    obtain ⟨eps, heps, hdiff⟩ :=
      zero_resolvent_differentiable_near_nonpole_v13
        g (by simpa [RightHalfPlaneV13] using hw) hpole
    have han : AnalyticAt ℂ (WeilZeroResolventV12 g) w := by
      apply hdiff.analyticAt
      exact Metric.ball_mem_nhds w (by linarith)
    exact han.meromorphicAt


theorem laplace_resolvent_seed_eventuallyEq_v13
    (g : WeilCompactSmoothGV1) :
    WeilZeroKernelLaplaceV12 g =ᶠ[𝓝 (1 : ℂ)]
      WeilZeroResolventV12 g := by
  let S : Set ℂ := {w : ℂ | (1 / 2 : ℝ) < w.re}
  have hSopen : IsOpen S := by
    rw [show S = Complex.re ⁻¹' Ioi (1 / 2 : ℝ) by
      ext w
      simp [S]]
    exact Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have h1S : (1 : ℂ) ∈ S := by
    show (1 / 2 : ℝ) < (1 : ℂ).re
    norm_num
  filter_upwards [hSopen.mem_nhds h1S] with w hw
  exact zero_kernel_laplace_eq_resolvent_v12 g w hw

theorem no_zero_re_gt_half_of_final_sign_v13
    (h : FinalSignResidualV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    ¬ (1 / 2 : ℝ) < rho.1.re := by
  intro hrho

  obtain ⟨g, hm, hcoef10⟩ :=
    exists_nonzero_zero_coefficient_v11 rho
  have hcoef11 : WeilZeroCoefficientV11 g rho ≠ 0 := by
    rw [zero_coefficient_v10_eq_v11 g rho] at hcoef10
    exact hcoef10

  let y : ℂ := WeilCenteredZeroExponentV12 rho
  have hy : y ∈ RightHalfPlaneV13 := by
    dsimp [y, RightHalfPlaneV13, WeilCenteredZeroExponentV12]
    simp
    linarith

  have hLapAnal :
      AnalyticOnNhd ℂ (WeilZeroKernelLaplaceV12 g) RightHalfPlaneV13 := by
    simpa [RightHalfPlaneV13, ZeroLaplaceRightHalfPlaneV12] using
      zero_kernel_laplace_analyticOnNhd_v12 h g hm

  have hLapMer :
      MeromorphicOn (WeilZeroKernelLaplaceV12 g) RightHalfPlaneV13 :=
    hLapAnal.meromorphicOn

  have hResMer :
      MeromorphicOn (WeilZeroResolventV12 g) RightHalfPlaneV13 :=
    zero_resolvent_meromorphicOn_rightHalfPlane_v13 g

  have hx : (1 : ℂ) ∈ RightHalfPlaneV13 := by
    simp [RightHalfPlaneV13]

  have hseed :
      WeilZeroKernelLaplaceV12 g =ᶠ[𝓝 (1 : ℂ)]
        WeilZeroResolventV12 g :=
    laplace_resolvent_seed_eventuallyEq_v13 g

  have heq :
      WeilZeroKernelLaplaceV12 g =ᶠ[𝓝[≠] y]
        WeilZeroResolventV12 g :=
    eventuallyEq_nhdsNE_of_meromorphicOn_of_seed
      hLapMer hResMer rightHalfPlane_isPreconnected_v13
      hx hy hseed

  have hordEq :
      meromorphicOrderAt (WeilZeroKernelLaplaceV12 g) y =
        meromorphicOrderAt (WeilZeroResolventV12 g) y :=
    meromorphicOrderAt_congr heq

  have hLapNonneg :
      0 ≤ meromorphicOrderAt (WeilZeroKernelLaplaceV12 g) y :=
    (hLapAnal y hy).meromorphicOrderAt_nonneg

  have hResNonneg :
      0 ≤ meromorphicOrderAt (WeilZeroResolventV12 g) y := by
    rw [← hordEq]
    exact hLapNonneg

  have hResOrder :
      meromorphicOrderAt (WeilZeroResolventV12 g) y = (-1 : ℤ) := by
    simpa [y] using
      zero_resolvent_order_eq_neg_one_v13 g rho hcoef11

  rw [hResOrder] at hResNonneg
  have hle : (0 : ℤ) ≤ -1 := by exact_mod_cast hResNonneg
  omega


def reflectedNontrivialZeroV13
    (rho : RiemannNontrivialZeroIndexV2) :
    RiemannNontrivialZeroIndexV2 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2

  have hnotNegNat : ∀ n : ℕ, rho.1 ≠ -(n : ℂ) := by
    intro n hn
    have hpos : 0 < rho.1.re := hstrip.1
    rw [hn] at hpos
    have hnonpos : (-(n : ℂ)).re ≤ 0 := by
      simp
    exact (not_lt_of_ge hnonpos) hpos

  have hrho1 : rho.1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.2]

  have hzref :
      riemannZeta (1 - rho.1) = 0 := by
    have hfe :=
      riemannZeta_one_sub (s := rho.1) hnotNegNat hrho1
    simpa [rho.2.1] using hfe

  have hrefpos : 0 < (1 - rho.1).re := by
    simp
    linarith [hstrip.2]

  have hrefNontriv :
      ¬ ∃ n : ℕ, (1 - rho.1) = -(2 : ℂ) * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at hrefpos
    have hnonpos :
        (-(2 : ℂ) * ((n : ℂ) + 1)).re ≤ 0 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp
      linarith
    exact (not_lt_of_ge hnonpos) hrefpos

  exact ⟨1 - rho.1, hzref, hrefNontriv⟩

theorem all_nontrivial_zeros_critical_of_final_sign_v13
    (h : FinalSignResidualV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    rho.1.re = 1 / 2 := by
  have hright :
      rho.1.re ≤ (1 / 2 : ℝ) :=
    le_of_not_gt (no_zero_re_gt_half_of_final_sign_v13 h rho)

  let sigma : RiemannNontrivialZeroIndexV2 :=
    reflectedNontrivialZeroV13 rho

  have hsigmaRight :
      sigma.1.re ≤ (1 / 2 : ℝ) :=
    le_of_not_gt (no_zero_re_gt_half_of_final_sign_v13 h sigma)

  have hsigmaRe :
      sigma.1.re = 1 - rho.1.re := by
    rfl

  rw [hsigmaRe] at hsigmaRight
  linarith

theorem final_sign_implies_rh_v13
    (h : FinalSignResidualV1) :
    RiemannHypothesis := by
  intro s hz htriv hone
  let rho : RiemannNontrivialZeroIndexV2 :=
    ⟨s, hz, htriv⟩
  simpa [rho] using
    all_nontrivial_zeros_critical_of_final_sign_v13 h rho

/-- Both directions: the restricted-Weil final sign residual is equivalent to
Mathlib's `RiemannHypothesis` (the reverse direction is the V11 producer). -/
theorem final_sign_iff_rh_v13 :
    FinalSignResidualV1 ↔ RiemannHypothesis :=
  ⟨final_sign_implies_rh_v13,
    AEGIS.WeilRHImpliesFinalSignV11.rh_implies_final_sign_residual_v11⟩


/-- Exact gate-typed restricted Weil criterion: the universal canonical
zero-quadratic sign is equivalent to the final sign residual already consumed
by the V13 pole contradiction. -/
theorem universal_zero_quadratic_implies_rh_v13
    (hU : UniversalZeroQuadraticNonnegativeV10) :
    RiemannHypothesis :=
  final_sign_implies_rh_v13
    (universal_zero_quadratic_iff_final_sign_v10.mp hU)

/-- The V13 closure inhabits the exact restricted-criterion field required by
the repository Millennium gate. -/
theorem restricted_weil_criterion_kernel_bridge_v13 :
    RestrictedWeilCriterionKernelBridgeV10 :=
  universal_zero_quadratic_implies_rh_v13


end AEGIS.V13Scratch
