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

import RHZeroKernelBoundV11
import WeilFixedLineKernelIntegralV6
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
AEGIS Ω — Laplace transform of the canonical zero translation kernel V12.

For lambda_rho = rho - 1/2 and
  a_rho = m_rho M(g)(rho) conj(M(g)(1-conj rho)),
the V11 kernel is
  K_g(t) = sum_rho a_rho exp(lambda_rho t).

On Re(w) > 1/2, absolute convergence permits a genuine sum/integral
interchange on t>0.  This module proves

  ∫_0^∞ exp(-w t) K_g(t) dt
    = sum_rho a_rho / (w - lambda_rho).

This is the initial half-plane identity needed for the Laplace-pole
continuation argument in the restricted Weil criterion.  No continuation
across Re(w)=1/2 and no RH conclusion is asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHZeroKernelLaplaceV12

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11

/-- Centered zero exponent lambda = rho - 1/2. -/
def WeilCenteredZeroExponentV12
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  rho.1 - (1 / 2 : ℂ)

/-- Every centered nontrivial zero lies in the strict half-strip
-1/2 < Re lambda < 1/2. -/
theorem centered_zero_re_mem_v12
    (rho : RiemannNontrivialZeroIndexV2) :
    -(1 / 2 : ℝ) < (WeilCenteredZeroExponentV12 rho).re ∧
      (WeilCenteredZeroExponentV12 rho).re < (1 / 2 : ℝ) := by
  have hs :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  unfold WeilCenteredZeroExponentV12
  simp only [Complex.sub_re, Complex.ofReal_re]
  constructor <;> linarith

/-- Absolute summability of the zero coefficients, inherited from the
repository's compact-smooth autocorrelation zero summability theorem. -/
theorem zero_coefficient_norm_summable_v12
    (g : WeilCompactSmoothGV1) :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      ‖WeilZeroCoefficientV11 g rho‖) := by
  change Summable
    (fun rho : RiemannNontrivialZeroIndexV2 =>
      ‖WeilZeroIndexSummandV1
        (WeilAutocorrelationCompactSmoothV1 g).1 rho‖)
  exact
    weil_compact_smooth_zero_norm_summable_v1
      (WeilAutocorrelationCompactSmoothV1 g)

/-- One zero's Laplace integrand. -/
def WeilZeroLaplaceTermV12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2) (t : ℝ) : ℂ :=
  WeilZeroCoefficientV11 g rho *
    Complex.exp
      (-((w - WeilCenteredZeroExponentV12 rho) * (t : ℂ)))

/-- One Laplace term is integrable whenever the Laplace parameter is to the
right of the zero exponent. -/
theorem zero_laplace_term_integrable_v12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2)
    (hw : (WeilCenteredZeroExponentV12 rho).re < w.re) :
    IntegrableOn (WeilZeroLaplaceTermV12 g w rho) (Ioi (0 : ℝ)) := by
  have hneg :
      (-(w - WeilCenteredZeroExponentV12 rho)).re < 0 := by
    simp
    linarith
  have he :=
    integrableOn_exp_mul_complex_Ioi
      (a := -(w - WeilCenteredZeroExponentV12 rho))
      hneg 0
  refine he.const_mul (WeilZeroCoefficientV11 g rho) |>.congr_fun ?_
    measurableSet_Ioi
  intro t ht
  unfold WeilZeroLaplaceTermV12
  congr 2
  push_cast
  ring

/-- Exact integral of one Laplace term. -/
theorem zero_laplace_term_integral_v12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2)
    (hw : (WeilCenteredZeroExponentV12 rho).re < w.re) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      WeilZeroLaplaceTermV12 g w rho) =
      WeilZeroCoefficientV11 g rho /
        (w - WeilCenteredZeroExponentV12 rho) := by
  have hneg :
      (-(w - WeilCenteredZeroExponentV12 rho)).re < 0 := by
    simp
    linarith
  unfold WeilZeroLaplaceTermV12
  rw [integral_const_mul]
  have h :=
    integral_exp_mul_complex_Ioi
      (a := -(w - WeilCenteredZeroExponentV12 rho))
      hneg 0
  have hfun :
      (fun t : ℝ =>
        Complex.exp
          (-((w - WeilCenteredZeroExponentV12 rho) * (t : ℂ)))) =
      (fun t : ℝ =>
        Complex.exp
          ((-(w - WeilCenteredZeroExponentV12 rho)) * t)) := by
    funext t
    congr 1
    push_cast
    ring
  rw [hfun, h]
  have hden :
      w - WeilCenteredZeroExponentV12 rho ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  simp [hden]
  field_simp [hden]
  ring

/-- Norm integral of one Laplace term. -/
theorem zero_laplace_term_norm_integral_v12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2)
    (hw : (WeilCenteredZeroExponentV12 rho).re < w.re) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      ‖WeilZeroLaplaceTermV12 g w rho t‖) =
      ‖WeilZeroCoefficientV11 g rho‖ /
        (w.re - (WeilCenteredZeroExponentV12 rho).re) := by
  let delta : ℝ :=
    w.re - (WeilCenteredZeroExponentV12 rho).re
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hfun :
      (fun t : ℝ =>
        ‖WeilZeroLaplaceTermV12 g w rho t‖) =
      (fun t : ℝ =>
        ‖WeilZeroCoefficientV11 g rho‖ *
          Real.exp (-delta * t)) := by
    funext t
    unfold WeilZeroLaplaceTermV12
    rw [norm_mul, Complex.norm_exp]
    congr 1
    congr 1
    dsimp [delta]
    simp
    ring
  rw [hfun, integral_const_mul,
    integral_exp_mul_Ioi (a := -delta) (by linarith) 0]
  simp [hdelta.ne']
  field_simp [hdelta.ne']
  ring

/-- The family of norm integrals is summable uniformly on each half-plane
Re(w)>1/2. -/
theorem zero_laplace_integral_norm_summable_v12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (hw : (1 / 2 : ℝ) < w.re) :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      ∫ t : ℝ in Ioi (0 : ℝ),
        ‖WeilZeroLaplaceTermV12 g w rho t‖) := by
  let D : ℝ := w.re - (1 / 2 : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    linarith

  have hbase := zero_coefficient_norm_summable_v12 g
  have hmajor :
      Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
        (1 / D) * ‖WeilZeroCoefficientV11 g rho‖) :=
    hbase.mul_left (1 / D)

  refine Summable.of_nonneg_of_le
    (fun rho => integral_nonneg (fun _ => norm_nonneg _))
    (fun rho => ?_) hmajor

  have hrho :=
    (centered_zero_re_mem_v12 rho).2
  rw [zero_laplace_term_norm_integral_v12 g w rho
    (hrho.trans hw)]
  have hden :
      D ≤ w.re - (WeilCenteredZeroExponentV12 rho).re := by
    dsimp [D]
    linarith
  have hdenpos :
      0 < w.re - (WeilCenteredZeroExponentV12 rho).re := by
    linarith
  have hinv :
      1 / (w.re - (WeilCenteredZeroExponentV12 rho).re) ≤ 1 / D := by
    exact one_div_le_one_div_of_le hD hden
  calc
    ‖WeilZeroCoefficientV11 g rho‖ /
        (w.re - (WeilCenteredZeroExponentV12 rho).re)
      =
      (1 / (w.re - (WeilCenteredZeroExponentV12 rho).re)) *
        ‖WeilZeroCoefficientV11 g rho‖ := by ring
    _ ≤ (1 / D) * ‖WeilZeroCoefficientV11 g rho‖ := by
      gcongr

/-- Pointwise, summing the Laplace terms recovers exp(-wt) K_g(t). -/
theorem tsum_zero_laplace_term_eq_kernel_v12
    (g : WeilCompactSmoothGV1) (w : ℂ) (t : ℝ) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroLaplaceTermV12 g w rho t) =
      Complex.exp (-(w * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t := by
  have hsum := zero_translation_kernel_summable_v11 g t
  unfold WeilZeroTranslationKernelV11
  rw [← hsum.tsum_mul_left (Complex.exp (-(w * (t : ℂ))))]
  apply tsum_congr
  intro rho
  unfold WeilZeroLaplaceTermV12 WeilZeroTranslationFactorV11
    WeilCenteredZeroExponentV12
  rw [← Complex.exp_add]
  ring_nf
  congr 1
  ring

/-- Resolvent sum on the initial right half-plane. -/
def WeilZeroResolventV12
    (g : WeilCompactSmoothGV1) (w : ℂ) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    WeilZeroCoefficientV11 g rho /
      (w - WeilCenteredZeroExponentV12 rho)

/-- Laplace transform of the zero translation kernel. -/
def WeilZeroKernelLaplaceV12
    (g : WeilCompactSmoothGV1) (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi (0 : ℝ),
    Complex.exp (-(w * (t : ℂ))) *
      WeilZeroTranslationKernelV11 g t

/-- Exact Laplace/resolvent identity on Re(w)>1/2. -/
theorem zero_kernel_laplace_eq_resolvent_v12
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (hw : (1 / 2 : ℝ) < w.re) :
    WeilZeroKernelLaplaceV12 g w =
      WeilZeroResolventV12 g w := by
  have hint :
      ∀ rho : RiemannNontrivialZeroIndexV2,
        Integrable
          (WeilZeroLaplaceTermV12 g w rho)
          (volume.restrict (Ioi (0 : ℝ))) := by
    intro rho
    exact
      zero_laplace_term_integrable_v12 g w rho
        ((centered_zero_re_mem_v12 rho).2.trans hw)

  have hnorm :=
    zero_laplace_integral_norm_summable_v12 g w hw

  have hswap :=
    integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Ioi (0 : ℝ)))
      hint hnorm

  unfold WeilZeroKernelLaplaceV12 WeilZeroResolventV12

  calc
    (∫ t : ℝ in Ioi (0 : ℝ),
      Complex.exp (-(w * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t)
      =
    ∫ t : ℝ in Ioi (0 : ℝ),
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroLaplaceTermV12 g w rho t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact (tsum_zero_laplace_term_eq_kernel_v12 g w t).symm
    _ =
    ∑' rho : RiemannNontrivialZeroIndexV2,
      ∫ t : ℝ in Ioi (0 : ℝ),
        WeilZeroLaplaceTermV12 g w rho := hswap.symm
    _ =
    ∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroCoefficientV11 g rho /
        (w - WeilCenteredZeroExponentV12 rho) := by
          apply tsum_congr
          intro rho
          exact zero_laplace_term_integral_v12 g w rho
            ((centered_zero_re_mem_v12 rho).2.trans hw)

end AEGIS.RHZeroKernelLaplaceV12

#print axioms AEGIS.RHZeroKernelLaplaceV12.centered_zero_re_mem_v12
#print axioms AEGIS.RHZeroKernelLaplaceV12.zero_laplace_integral_norm_summable_v12
#print axioms AEGIS.RHZeroKernelLaplaceV12.tsum_zero_laplace_term_eq_kernel_v12
#print axioms AEGIS.RHZeroKernelLaplaceV12.zero_kernel_laplace_eq_resolvent_v12
