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

/-
Fork-local exact-head compatibility overlay.
Authoritative source:
Aegis-Omega/AEGIS-OMEGA@589adf0480bd4d7c12c9828027ea6228398377f4
source blob: 547eee56ef0801714ef99a5cb31cbb2a015a279c
The theorem statements are unchanged; only pinned Lean/Mathlib elaboration
repairs are applied.
-/

import RHZeroKernelLaplaceV12
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — continuity and right-half-plane analyticity of the zero-kernel
Laplace transform V12.

The V12 zero translation kernel is a locally uniformly convergent sum of
continuous exponentials.  This module proves its continuity by an explicit
local Weierstrass M-test.

Assuming the exact final-sign residual, the four-phase theorem supplies the
global bound
  ||K_g(t)|| <= 2 Q_g  for all real t.
Therefore, for every w with Re(w)>0, both
  exp(-w t) K_g(t)
and its w-derivative are dominated on t>0 by integrable exponential tails.
Differentiation under the integral proves that the Laplace transform is
holomorphic on the full open right half-plane.

This is the analytic side of the pole obstruction.  No residue contradiction
or RH conclusion is asserted in this module.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHZeroKernelLaplaceAnalyticV12

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelBoundV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHFinalClosureV1

/-- Local uniform majorant for a single zero term on a compact real interval. -/
private theorem zero_kernel_term_local_bound_v12
    (g : WeilCompactSmoothGV1) (t0 : ℝ)
    (rho : RiemannNontrivialZeroIndexV2)
    {t : ℝ} (ht : t ∈ Icc (t0 - 1) (t0 + 1)) :
    ‖WeilZeroCoefficientV11 g rho *
        WeilZeroTranslationFactorV11 rho t‖
      ≤
      (Real.exp ((|t0| + 1) / 2)) *
        ‖WeilZeroCoefficientV11 g rho‖ := by
  rw [norm_mul]
  have hlambda :
      |(WeilCenteredZeroExponentV12 rho).re| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    have hs := centered_zero_re_mem_v12 rho
    exact ⟨hs.1.le, hs.2.le⟩
  have htAbs : |t| ≤ |t0| + 1 := by
    rcases ht with ⟨htl, htu⟩
    rw [abs_le]
    constructor
    · have h1 : -(|t0| + 1) ≤ t0 - 1 := by
        have := neg_abs_le t0
        linarith
      exact h1.trans htl
    · have h1 : t0 + 1 ≤ |t0| + 1 := by
        linarith [le_abs_self t0]
      exact htu.trans h1
  have hexpRe :
      ((WeilCenteredZeroExponentV12 rho) * (t : ℂ)).re
        ≤ (|t0| + 1) / 2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    calc
      (WeilCenteredZeroExponentV12 rho).re * t
        ≤ |(WeilCenteredZeroExponentV12 rho).re * t| :=
          le_abs_self _
      _ =
        |(WeilCenteredZeroExponentV12 rho).re| * |t| := abs_mul _ _
      _ ≤ (1 / 2 : ℝ) * (|t0| + 1) := by
        gcongr
      _ = (|t0| + 1) / 2 := by ring
  have hfactor :
      ‖WeilZeroTranslationFactorV11 rho t‖
        ≤ Real.exp ((|t0| + 1) / 2) := by
    unfold WeilZeroTranslationFactorV11
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hexpRe
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hfactor
      (norm_nonneg (WeilZeroCoefficientV11 g rho)))

/-- The canonical zero translation kernel is a continuous function of the
real translation parameter. -/
theorem zero_translation_kernel_continuous_v12
    (g : WeilCompactSmoothGV1) :
    Continuous (WeilZeroTranslationKernelV11 g) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let C : ℝ := Real.exp ((|t0| + 1) / 2)
  let u : RiemannNontrivialZeroIndexV2 → ℝ := fun rho =>
    C * ‖WeilZeroCoefficientV11 g rho‖
  have hu : Summable u := by
    exact (zero_coefficient_norm_summable_v12 g).mul_left C
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          ∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroCoefficientV11 g rho *
              WeilZeroTranslationFactorV11 rho t)
        (Icc (t0 - 1) (t0 + 1)) := by
    apply continuousOn_tsum
    · intro rho
      apply Continuous.continuousOn
      unfold WeilZeroTranslationFactorV11
      fun_prop
    · exact hu
    · intro rho t ht
      exact zero_kernel_term_local_bound_v12 g t0 rho ht
  have hnhds :
      Icc (t0 - 1) (t0 + 1) ∈ 𝓝 t0 := by
    exact Icc_mem_nhds (by linarith) (by linarith)
  unfold WeilZeroTranslationKernelV11
  exact hcont.continuousAt hnhds

/-- Open right half-plane used by the bounded-kernel Laplace transform. -/
def ZeroLaplaceRightHalfPlaneV12 : Set ℂ :=
  {w : ℂ | 0 < w.re}

theorem zeroLaplaceRightHalfPlane_isOpen_v12 :
    IsOpen ZeroLaplaceRightHalfPlaneV12 := by
  rw [show ZeroLaplaceRightHalfPlaneV12 =
      Complex.re ⁻¹' Ioi (0 : ℝ) by
    ext w
    simp [ZeroLaplaceRightHalfPlaneV12]]
  exact Complex.continuous_re.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi

/-- Final-sign bound in a compact form used by the Laplace estimates. -/
private theorem zero_kernel_uniform_bound_v12
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) (t : ℝ) :
    ‖WeilZeroTranslationKernelV11 g t‖
      ≤ 2 * (WeilAutocorrelationZeroQuadraticV11 g).re :=
  final_sign_zero_kernel_norm_bound_v11 h g t hm

/-- The bounded zero kernel has an integrable Laplace transform for every
parameter in Re(w)>0. -/
theorem zero_kernel_laplace_integrable_of_final_sign_v12
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.exp (-(w * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t)
      (Ioi (0 : ℝ)) := by
  let B : ℝ := 2 * (WeilAutocorrelationZeroQuadraticV11 g).re
  have hQ :
      0 ≤ (WeilAutocorrelationZeroQuadraticV11 g).re :=
    final_sign_zero_quadratic_nonnegative_v11 h g hm
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmajor :
      IntegrableOn
        (fun t : ℝ => B * Real.exp (-w.re * t))
        (Ioi (0 : ℝ)) := by
    exact
      (integrableOn_exp_mul_Ioi (a := -w.re) (by linarith) 0).const_mul B
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))) *
            WeilZeroTranslationKernelV11 g t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable).restrict
  refine hmajor.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall (fun t ht => by
    rw [norm_mul, Complex.norm_exp]
    have hK := zero_kernel_uniform_bound_v12 h g hm t
    have hre :
        (-(w * (t : ℂ))).re = -w.re * t := by
      simp
    rw [hre]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hK (Real.exp_nonneg (-w.re * t))))

/-- An integrable first-moment exponential tail used to dominate the
w-derivative locally. -/
private theorem first_moment_exp_tail_integrable_v12
    (δ B : ℝ) (hδ : 0 < δ) :
    IntegrableOn
      (fun t : ℝ => B * (t * Real.exp (-(δ * t))))
      (Ioi (0 : ℝ)) := by
  by_cases hB : B = 0
  · simp [hB]
  have hbase :
      IntegrableOn
        (fun t : ℝ => t * Real.exp (-(δ * t)))
        (Ioi (0 : ℝ)) := by
    have key :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := (2 : ℝ)) (r := δ) (by norm_num) hδ
    have hint :
        IntegrableOn
          (fun t : ℝ =>
            t ^ ((2 : ℝ) - 1) * Real.exp (-(δ * t)))
          (Ioi (0 : ℝ)) :=
      .of_integral_ne_zero (by
        rw [key]
        positivity)
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hint
  exact hbase.const_mul B

/-- Differentiability of the bounded-kernel Laplace transform at every point
of the open right half-plane. -/
theorem zero_kernel_laplace_differentiableAt_v12
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (w0 : ℂ) (hw0 : 0 < w0.re) :
    DifferentiableAt ℂ (WeilZeroKernelLaplaceV12 g) w0 := by
  let δ : ℝ := w0.re / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let B : ℝ := 2 * (WeilAutocorrelationZeroQuadraticV11 g).re
  have hQ :
      0 ≤ (WeilAutocorrelationZeroQuadraticV11 g).re :=
    final_sign_zero_quadratic_nonnegative_v11 h g hm
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity

  let F : ℂ → ℝ → ℂ := fun w t =>
    Complex.exp (-(w * (t : ℂ))) *
      WeilZeroTranslationKernelV11 g t
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ)) *
      Complex.exp (-(w * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t
  let bound : ℝ → ℝ := fun t =>
    B * (t * Real.exp (-(δ * t)))

  have hs : Metric.ball w0 δ ∈ 𝓝 w0 :=
    Metric.ball_mem_nhds _ hδ

  have hFmeas :
      ∀ᶠ w in 𝓝 w0,
        AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (0 : ℝ))) := by
    exact Filter.Eventually.of_forall (fun w => by
      apply AEStronglyMeasurable.restrict
      exact
        ((by fun_prop :
          Continuous (fun t : ℝ =>
            Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
          (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable))

  have hFint :
      Integrable (F w0) (volume.restrict (Ioi (0 : ℝ))) := by
    exact zero_kernel_laplace_integrable_of_final_sign_v12
      h g hm w0 hw0

  have hF'meas :
      AEStronglyMeasurable (F' w0)
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply AEStronglyMeasurable.restrict
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          (-(t : ℂ)) *
            Complex.exp (-(w0 * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable)

  have hbound :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ, ‖F' w t‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      have ht0 : 0 ≤ t := le_of_lt ht
      have hdist : ‖w - w0‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hreDiff : |w.re - w0.re| ≤ ‖w - w0‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w0)
      have hwre : δ ≤ w.re := by
        have hlo := (abs_lt.mp (lt_of_le_of_lt hreDiff hdist)).1
        dsimp [δ] at hlo ⊢
        linarith
      have hK := zero_kernel_uniform_bound_v12 h g hm t
      unfold F' bound
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_exp]
      have hre :
          (-(w * (t : ℂ))).re = -w.re * t := by
        simp
      rw [hre]
      have hexp :
          Real.exp (-w.re * t) ≤ Real.exp (-(δ * t)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        t * Real.exp (-w.re * t) *
            ‖WeilZeroTranslationKernelV11 g t‖
          ≤ t * Real.exp (-(δ * t)) * B := by
              gcongr
        _ = B * (t * Real.exp (-(δ * t))) := by ring)

  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    exact first_moment_exp_tail_integrable_v12 δ B hδ

  have hdiff :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ,
          HasDerivAt (F · t) (F' w t) w := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      unfold F F'
      have hExp :
          HasDerivAt
            (fun z : ℂ => Complex.exp (-(z * (t : ℂ))))
            (-(t : ℂ) *
              Complex.exp (-(w * (t : ℂ)))) w := by
        simpa [mul_comm] using
          ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp
      exact hExp.mul_const
        (WeilZeroTranslationKernelV11 g t))

  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hFmeas hFint hF'meas hbound hboundInt hdiff

  have hder := main.2.differentiableAt
  change DifferentiableAt ℂ
    (fun w : ℂ =>
      ∫ t : ℝ in Ioi (0 : ℝ),
        Complex.exp (-(w * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t) w0
  simpa [F] using hder

/-- Under final sign, the zero-kernel Laplace transform is holomorphic on the
entire open right half-plane. -/
theorem zero_kernel_laplace_analyticOnNhd_v12
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    AnalyticOnNhd ℂ
      (WeilZeroKernelLaplaceV12 g)
      ZeroLaplaceRightHalfPlaneV12 := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    exact
      (zero_kernel_laplace_differentiableAt_v12
        h g hm w hw).differentiableWithinAt
  · exact zeroLaplaceRightHalfPlane_isOpen_v12

end AEGIS.RHZeroKernelLaplaceAnalyticV12

#print axioms AEGIS.RHZeroKernelLaplaceAnalyticV12.zero_translation_kernel_continuous_v12
#print axioms AEGIS.RHZeroKernelLaplaceAnalyticV12.zero_kernel_laplace_integrable_of_final_sign_v12
#print axioms AEGIS.RHZeroKernelLaplaceAnalyticV12.zero_kernel_laplace_differentiableAt_v12
#print axioms AEGIS.RHZeroKernelLaplaceAnalyticV12.zero_kernel_laplace_analyticOnNhd_v12
