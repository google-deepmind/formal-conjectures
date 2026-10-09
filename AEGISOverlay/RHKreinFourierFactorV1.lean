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

import RHKreinSymbolIntegrationV1
import RHKreinFactorV13
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier multiplier and angular Krein pairing

The derivative factor is transported to angular frequency with the exact
Mathlib scaling. The actual existing Krein pairing is transported by the
same change of variables. Neither theorem consumes a numerical certificate.
-/

open Set MeasureTheory Complex FourierTransform
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFourierFactorV1

/-- The Jacobian for angular frequency is exactly 2*pi in this direction. -/
theorem angular_integral (f : ℝ → ℂ) :
    (∫ t : ℝ, f (-t / (2 * Real.pi))) = (2 * Real.pi : ℂ) * ∫ ξ : ℝ, f ξ := by
  have he : (fun t : ℝ => f (-t / (2 * Real.pi))) =
      (fun t : ℝ => f (t / (-(2 * Real.pi)))) := by
    funext t
    congr 1
    ring
  rw [he, Measure.integral_comp_div]
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Complex.real_smul]
  push_cast
  rfl

/-- The genuine-function Krein correction pairs to zero with angular Fourier
mass. All support and integrability hypotheses match the existing theorem. -/
theorem angular_krein_pairing (G : ℝ → ℂ) (a b : ℝ) (hG : Integrable G)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Set.Ioo a b)
    (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hHs : ∀ u, |u| < b - a → H u = 0) :
    (∫ t : ℝ, (Complex.normSq (𝓕 G (-t / (2 * Real.pi))) : ℂ) *
      𝓕 H (-t / (2 * Real.pi))) = 0 := by
  have h := AEGIS.RHKreinPairingV13.krein_pairing G a b hG hsupp H hHc hH hFH hHs
  rw [angular_integral (fun ξ => (Complex.normSq (𝓕 G ξ) : ℂ) * 𝓕 H ξ), h, mul_zero]

/-- Fourier linearity on the particular integrable differential expression. -/
theorem fourier_differential_factor (χ : ℝ → ℂ)
    (hχ : Integrable χ) (hχ' : Integrable (deriv χ))
    (hχ'' : Integrable (deriv (deriv χ)))
    (hdχ : Differentiable ℝ χ) (hdχ' : Differentiable ℝ (deriv χ)) (t : ℝ) :
    𝓕 (fun x => deriv (deriv χ) x - (1 / 4 : ℂ) * χ x) (-t / (2 * Real.pi)) =
      -(((t ^ 2 + 1 / 4 : ℝ) : ℂ)) * 𝓕 χ (-t / (2 * Real.pi)) := by
  have hlin := VectorFourier.fourierIntegral_add
    (e := Real.fourierChar) (μ := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hχ'' (hχ.const_mul (-1 / 4 : ℂ))
  have hscaled := VectorFourier.fourierIntegral_const_smul
    Real.fourierChar volume (innerₗ ℝ) χ (-1 / 4 : ℂ)
  have hF : 𝓕 (fun x => deriv (deriv χ) x - (1 / 4 : ℂ) * χ x) =
      fun ξ => 𝓕 (deriv (deriv χ)) ξ - (1 / 4 : ℂ) * 𝓕 χ ξ := by
    funext ξ
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_div, neg_mul, ← sub_eq_add_neg] using congrFun (hlin.trans
        (congrArg (fun v => VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ ℝ) (deriv (deriv χ)) + v) hscaled)) ξ
  rw [hF, Real.fourier_deriv hχ' hdχ' hχ'', Real.fourier_deriv hχ hdχ hχ']
  simp only [smul_eq_mul]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hp]
  simp only [Complex.I_sq]
  ring

/-- Every actual moment-zero packet has a smooth compactly supported factor
on the same window, with the exact squared angular Fourier multiplier. -/
theorem actual_packet_fourier_factor
    (g : WeilCompactSmoothGV1) (a b : ℝ) (hab : a ≤ b)
    (hs : tsupport (AEGIS.WeilLogCoordinateIsometryV21.logLift g.1) ⊆ Icc a b)
    (hm : WeilMomentConditionsV1 g) :
    ∃ χ : ℝ → ℂ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Icc a b ∧ Integrable χ ∧
      ∀ t : ℝ,
        Complex.normSq (𝓕 (AEGIS.WeilLogCoordinateIsometryV21.logLift g.1)
          (-t / (2 * Real.pi))) =
        (t ^ 2 + 1 / 4) ^ 2 * Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) := by
  let G := AEGIS.WeilLogCoordinateIsometryV21.logLift g.1
  have hG : ContDiff ℝ ∞ G := by
    have hg := g.2.1
    unfold G AEGIS.WeilLogCoordinateIsometryV21.logLift
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_id.div_const (2 : ℝ)).exp).mul
      (hg.comp Real.contDiff_exp)
  have hp : (∫ u : ℝ, (Real.exp (u / 2) : ℂ) * G u) = 0 := by
    change (∫ u : ℝ, (Real.exp (u / 2) : ℂ) * AEGIS.RHKreinFactorV13.lift g.1 u) = 0
    rw [AEGIS.RHKreinFactorV13.lift_moment_plus]
    exact hm.2
  have hn : (∫ u : ℝ, (Real.exp (-u / 2) : ℂ) * G u) = 0 := by
    change (∫ u : ℝ, (Real.exp (-u / 2) : ℂ) * AEGIS.RHKreinFactorV13.lift g.1 u) = 0
    rw [AEGIS.RHKreinFactorV13.lift_moment_minus]
    exact hm.1
  obtain ⟨χ, hc, hcs, heq⟩ :=
    AEGIS.RHKreinFactorV13.moment_zero_parametrization G a b hab hG hs hn hp
  have hcompact : HasCompactSupport χ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hcs
  have hc' := (contDiff_infty_iff_deriv.mp hc).2
  have hc'' := (contDiff_infty_iff_deriv.mp hc').2
  have hi : Integrable χ := hc.continuous.integrable_of_hasCompactSupport hcompact
  have hi' : Integrable (deriv χ) :=
    hc'.continuous.integrable_of_hasCompactSupport hcompact.deriv
  have hi'' : Integrable (deriv (deriv χ)) :=
    hc''.continuous.integrable_of_hasCompactSupport hcompact.deriv.deriv
  refine ⟨χ, hc, hcs, hi, fun t => ?_⟩
  have hfun : G = fun u => deriv (deriv χ) u - (1 / 4 : ℂ) * χ u := funext heq
  change Complex.normSq (𝓕 G (-t / (2 * Real.pi))) = _
  rw [hfun, fourier_differential_factor χ hi hi' hi''
    (contDiff_infty_iff_deriv.mp hc).1 (contDiff_infty_iff_deriv.mp hc').1]
  rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
  ring

end AEGIS.RHKreinFourierFactorV1

#print axioms AEGIS.RHKreinFourierFactorV1.angular_integral
#print axioms AEGIS.RHKreinFourierFactorV1.angular_krein_pairing
#print axioms AEGIS.RHKreinFourierFactorV1.fourier_differential_factor

#print axioms AEGIS.RHKreinFourierFactorV1.actual_packet_fourier_factor
