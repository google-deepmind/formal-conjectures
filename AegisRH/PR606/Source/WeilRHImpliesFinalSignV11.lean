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

import WeilAutocorrelationExplicitFormulaV10
import WeilZeroSideIdentificationV1
import WeilLogCoordinateIsometryV21
import MellinDecayEstimateV1
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
AEGIS Ω — RH implies the final Weil sign residual, V11.

This is a new theorem-producing lane, not a status bridge.

For g in the repository compact-smooth positive-half-line class, define

  h(t) = exp(t/2) g(exp t).

The critical-line Mellin profile of g is the Fourier transform of h reflected
in t.  The critical-line Mellin profile of the multiplicative autocorrelation
is the reflected ordinary convolution

  (conj(h ∘ neg)) * h.

The Fourier convolution theorem therefore gives

  M(Autocorrelation g)(1/2 + iγ)
    = M(g)(1/2 + iγ) * conj(M(g)(1/2 + iγ))
    = ‖M(g)(1/2 + iγ)‖².

Under Mathlib's RiemannHypothesis every nontrivial zeta zero lies on that
line, so every multiplicity-weighted zero summand is a nonnegative real.
Absolute summability already exists in the repository.  Hence the canonical
zero quadratic is nonnegative; the V10 whole explicit-formula bridge then
yields FinalSignResidualV1.

AUTHORITY_EFFECT = NONE.
The reverse implication is not asserted in this file.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators FourierTransform Convolution ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilRHImpliesFinalSignV11

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Positive logarithmic coordinate profile. -/
def CriticalLogProfileV11 (g : WeilCompactSmoothGV1) (t : ℝ) : ℂ :=
  logLift g.1 t

/-- Reflected conjugate profile used in the ordinary additive convolution. -/
def CriticalLogAdjointV11 (g : WeilCompactSmoothGV1) (t : ℝ) : ℂ :=
  conj (CriticalLogProfileV11 g (-t))

private theorem critical_log_profile_continuous_v11
    (g : WeilCompactSmoothGV1) :
    Continuous (CriticalLogProfileV11 g) := by
  unfold CriticalLogProfileV11 logLift
  fun_prop

private theorem critical_log_profile_hasCompactSupport_v11
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (CriticalLogProfileV11 g) := by
  let K : Set ℝ := Real.log '' tsupport g.1
  have hts : IsCompact (tsupport g.1) := by
    change IsCompact (closure (Function.support g.1))
    exact g.2.2.1
  have hlog : ContinuousOn Real.log (tsupport g.1) := by
    intro x hx
    exact (Real.continuousAt_log (ne_of_gt (g.2.2.2 hx))).continuousWithinAt
  have hK : IsCompact K := hts.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro t ht
  change
    Complex.ofReal (Real.exp (t / 2)) * g.1 (Real.exp t) ≠ 0 at ht
  have hg : g.1 (Real.exp t) ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht
    exact ht rfl
  have hmem : Real.exp t ∈ tsupport g.1 := subset_tsupport g.1 hg
  refine ⟨Real.exp t, hmem, ?_⟩
  simp

theorem critical_log_profile_integrable_v11
    (g : WeilCompactSmoothGV1) :
    Integrable (CriticalLogProfileV11 g) :=
  (critical_log_profile_continuous_v11 g).integrable_of_hasCompactSupport
    (critical_log_profile_hasCompactSupport_v11 g)

private theorem critical_log_adjoint_continuous_v11
    (g : WeilCompactSmoothGV1) :
    Continuous (CriticalLogAdjointV11 g) := by
  unfold CriticalLogAdjointV11
  exact continuous_conj.comp
    ((critical_log_profile_continuous_v11 g).comp continuous_neg)

private theorem critical_log_adjoint_hasCompactSupport_v11
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (CriticalLogAdjointV11 g) := by
  have hneg :
      HasCompactSupport
        (fun t : ℝ => CriticalLogProfileV11 g (-t)) := by
    have h :=
      (critical_log_profile_hasCompactSupport_v11 g).comp_homeomorph
        (Homeomorph.neg ℝ)
    simpa [Function.comp_def] using h
  exact hneg.comp_left (by simp)

theorem critical_log_adjoint_integrable_v11
    (g : WeilCompactSmoothGV1) :
    Integrable (CriticalLogAdjointV11 g) :=
  (critical_log_adjoint_continuous_v11 g).integrable_of_hasCompactSupport
    (critical_log_adjoint_hasCompactSupport_v11 g)

/-- The fixed-real-part Mellin profile at sigma=1/2 is the reflected positive
log profile. -/
theorem critical_mellin_profile_eq_log_reflection_v11
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    MellinWeightedLogProfileV1 g.1 (1 / 2) u =
      CriticalLogProfileV11 g (-u) := by
  unfold MellinWeightedLogProfileV1 MellinComplexWeightV1
    MellinWeightV1 MellinLogProfileV1 CriticalLogProfileV11 logLift
  simp [Complex.real_smul]
  congr 2
  ring

/-- Multiplicative autocorrelation becomes ordinary additive correlation after
the unitary logarithmic lift. -/
theorem autocorrelation_critical_profile_convolution_v11
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    MellinWeightedLogProfileV1 (WeilAutocorrelationV1 g) (1 / 2) u =
      ((CriticalLogAdjointV11 g) ⋆[mul ℂ ℂ]
        (CriticalLogProfileV11 g)) (-u) := by
  rw [convolution_def]
  unfold MellinWeightedLogProfileV1 MellinComplexWeightV1
    MellinWeightV1 MellinLogProfileV1 WeilAutocorrelationV1
  simp only [Complex.real_smul]
  have hExp :=
    integral_comp_exp
      (fun y : ℝ =>
        g.1 (Real.exp (-u) * y) * conj (g.1 y))
  rw [← hExp]
  rw [← integral_const_mul]
  have hneg :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun t : ℝ =>
        (mul ℂ ℂ)
          (CriticalLogAdjointV11 g t)
          (CriticalLogProfileV11 g (-u - t)))
  rw [← hneg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    unfold CriticalLogAdjointV11 CriticalLogProfileV11 logLift
    simp [Complex.real_smul]
    rw [← Real.exp_add]
    congr 1
    · ring_nf
    · congr 2 <;> ring)

/-- Fourier transform of the reflected-conjugate profile. -/
theorem fourier_critical_adjoint_v11
    (g : WeilCompactSmoothGV1) (ξ : ℝ) :
    𝓕 (CriticalLogAdjointV11 g) ξ =
      conj (𝓕 (CriticalLogProfileV11 g) ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  have hneg :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun t : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * t * ξ) * I)) *
          CriticalLogAdjointV11 g t)
  rw [← hneg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    unfold CriticalLogAdjointV11
    simp [map_mul, Complex.exp_conj]
    congr 1
    ring)

/-- Critical-line Mellin transform as Fourier transform of the reflected
positive log profile. -/
theorem mellin_critical_eq_fourier_log_v11
    (g : WeilCompactSmoothGV1) (γ : ℝ) :
    mellin g.1 (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) =
      𝓕 (fun u : ℝ => CriticalLogProfileV11 g (-u))
        (γ / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    zero_mul, sub_zero, add_im, mul_im, one_mul, zero_add]
  apply congrArg (fun F : ℝ → ℂ =>
    𝓕 F (γ / (2 * Real.pi)))
  funext u
  rw [critical_mellin_profile_eq_log_reflection_v11]

/-- The critical-line Mellin transform of the actual multiplicative
autocorrelation is a modulus square. -/
theorem autocorrelation_mellin_critical_normSq_v11
    (g : WeilCompactSmoothGV1) (γ : ℝ) :
    mellin (WeilAutocorrelationV1 g)
        (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) =
      (Complex.normSq
        (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I)) : ℂ) := by
  let A := WeilAutocorrelationCompactSmoothV1 g
  let H := CriticalLogProfileV11 g
  let Hstar := CriticalLogAdjointV11 g
  let ξ : ℝ := γ / (2 * Real.pi)

  have hmA := mellin_critical_eq_fourier_log_v11 A γ
  have hprof :
      (fun u : ℝ => CriticalLogProfileV11 A (-u)) =
        fun u : ℝ => (Hstar ⋆[mul ℂ ℂ] H) (-u) := by
    funext u
    have hw :=
      critical_mellin_profile_eq_log_reflection_v11 A u
    have hc :=
      autocorrelation_critical_profile_convolution_v11 g u
    change CriticalLogProfileV11 A (-u) =
      (Hstar ⋆[mul ℂ ℂ] H) (-u)
    rw [← hw]
    simpa [A, H, Hstar] using hc

  rw [hprof] at hmA
  have hconv :=
    Real.fourier_mul_convolution_eq
      (critical_log_adjoint_integrable_v11 g)
      (critical_log_profile_integrable_v11 g)
      ξ

  have hmG := mellin_critical_eq_fourier_log_v11 g γ
  have hnegFourier :
      𝓕 (fun u : ℝ => H (-u)) ξ = 𝓕 H (-ξ) := by
    have h :=
      Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ) H ξ
    simpa [Function.comp_def] using h

  have hadj :
      𝓕 Hstar (-ξ) = conj (𝓕 H (-ξ)) := by
    simpa [Hstar, H] using fourier_critical_adjoint_v11 g (-ξ)

  have hconvNeg :
      𝓕 (Hstar ⋆[mul ℂ ℂ] H) (-ξ) =
        conj (𝓕 H (-ξ)) * 𝓕 H (-ξ) := by
    have hc :=
      Real.fourier_mul_convolution_eq
        (critical_log_adjoint_integrable_v11 g)
        (critical_log_profile_integrable_v11 g)
        (-ξ)
    rw [hadj] at hc
    exact hc

  rw [hmA]
  have hmAneg :
      𝓕 (fun u : ℝ => (Hstar ⋆[mul ℂ ℂ] H) (-u)) ξ =
        𝓕 (Hstar ⋆[mul ℂ ℂ] H) (-ξ) := by
    have h :=
      Real.fourier_comp_linearIsometry
        (LinearIsometryEquiv.neg ℝ)
        (Hstar ⋆[mul ℂ ℂ] H) ξ
    simpa [Function.comp_def] using h
  rw [hmAneg, hconvNeg]
  rw [hmG, hnegFourier]
  push_cast
  have hmul :=
    Complex.mul_conj (𝓕 H (-ξ))
  apply Complex.ext
  · simp [Complex.normSq_apply]
    ring
  · simp

/-- Under RH, every canonical zero summand of the autocorrelation has
nonnegative real part. -/
theorem rh_zero_summand_nonnegative_v11
    (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    0 ≤ (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
  have hrho1 : rho.1 ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hcrit :
      rho.1.re = 1 / 2 :=
    hRH rho.1 rho.2.1 rho.2.2 hrho1
  have hrho :
      rho.1 =
        (((1 / 2 : ℝ) : ℂ) + (rho.1.im : ℂ) * I) := by
    apply Complex.ext
    · simpa [hcrit]
    · simp
  unfold WeilZeroIndexSummandV1
  rw [hrho, autocorrelation_mellin_critical_normSq_v11 g rho.1.im]
  simp [Complex.normSq_apply]
  positivity

/-- RH makes the entire canonical autocorrelation zero quadratic nonnegative. -/
theorem rh_zero_quadratic_nonnegative_v11
    (hRH : RiemannHypothesis)
    (g : WeilCompactSmoothGV1) :
    0 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hsum :=
    weil_compact_smooth_zero_summable_v1
      (WeilAutocorrelationCompactSmoothV1 g)
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg (fun rho => rh_zero_summand_nonnegative_v11 hRH g rho)

/-- NEW PRODUCER: Mathlib RH implies the repository final sign residual. -/
theorem rh_implies_final_sign_residual_v11
    (hRH : RiemannHypothesis) :
    FinalSignResidualV1 := by
  rw [final_sign_residual_iff_zero_quadratic_nonnegative_v10]
  intro g _
  exact rh_zero_quadratic_nonnegative_v11 hRH g

end AEGIS.WeilRHImpliesFinalSignV11

#print axioms AEGIS.WeilRHImpliesFinalSignV11.autocorrelation_mellin_critical_normSq_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_zero_summand_nonnegative_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_zero_quadratic_nonnegative_v11
#print axioms AEGIS.WeilRHImpliesFinalSignV11.rh_implies_final_sign_residual_v11
