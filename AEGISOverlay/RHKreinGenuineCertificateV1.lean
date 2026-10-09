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

import RHKreinFourierFactorV1
import RHKreinCertificateTransferV1

/-!
# Genuine Krein certificate consumer for the actual Weil quadratic

This module constructs the moment factor and both spectral masses, and
proves correction integrability and zero pairing from the existing Krein
theorem. The certificate inputs are only a genuine function H with the
stated regularity/support and a pointwise weighted symbol inequality.
No evenness assumption is needed: the second mass uses the reflected factor.
-/

open Set MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinGenuineCertificateV1

open AEGIS.RHKreinFourierFactorV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinCertificateTransferV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilDisjointEnergyV2

private theorem angular_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => f (-t / (2 * Real.pi))) := by
  have hne : (-(2 * Real.pi))⁻¹ ≠ 0 :=
    inv_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have h := hf.comp_mul_right' hne
  have he : (fun t : ℝ => f (-t / (2 * Real.pi))) =
      (fun t : ℝ => f (t * (-(2 * Real.pi))⁻¹)) := by
    funext t
    congr 1
    rw [div_eq_mul_inv, inv_neg]
    ring
  rw [he]
  exact h

private theorem spectral_pair_integrable (G H : ℝ → ℂ)
    (hG : Integrable G) (hFH : Integrable (𝓕 H)) :
    Integrable (fun ξ : ℝ => (Complex.normSq (𝓕 G ξ) : ℂ) * 𝓕 H ξ) := by
  have hc : Continuous (𝓕 G) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) G)
    exact VectorFourier.fourierIntegral_continuous (e := Real.fourierChar)
      (μ := volume) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hG
  have hn : Continuous (fun ξ : ℝ => (Complex.normSq (𝓕 G ξ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp hc)
  have hb : ∀ ξ : ℝ, ‖(Complex.normSq (𝓕 G ξ) : ℂ)‖ ≤ (∫ x : ℝ, ‖G x‖) ^ 2 := by
    intro ξ
    have hbound : ‖𝓕 G ξ‖ ≤ ∫ x : ℝ, ‖G x‖ := by
      change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) G ξ‖ ≤
        ∫ x : ℝ, ‖G x‖
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) G ξ
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    have hn0 : 0 ≤ ∫ x : ℝ, ‖G x‖ := integral_nonneg (fun x => norm_nonneg _)
    nlinarith [norm_nonneg (𝓕 G ξ)]
  exact hFH.bdd_mul hn.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The real correction integral is integrable and zero; the existing
complex pairing theorem is the sole source of the vanishing claim. -/
theorem real_angular_krein_pairing (G : ℝ → ℂ) (a b : ℝ)
    (hG : Integrable G) (hs : ∀ y, G y ≠ 0 → y ∈ Ioo a b)
    (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hHs : ∀ u, |u| < b - a → H u = 0) :
    Integrable (fun t : ℝ => (𝓕 H (-t / (2 * Real.pi))).re *
      Complex.normSq (𝓕 G (-t / (2 * Real.pi)))) ∧
    (∫ t : ℝ, (𝓕 H (-t / (2 * Real.pi))).re *
      Complex.normSq (𝓕 G (-t / (2 * Real.pi)))) = 0 := by
  have hi := angular_integrable (spectral_pair_integrable G H hG hFH)
  have he : ∀ t : ℝ,
      ((Complex.normSq (𝓕 G (-t / (2 * Real.pi))) : ℂ) *
        𝓕 H (-t / (2 * Real.pi))).re =
      (𝓕 H (-t / (2 * Real.pi))).re * Complex.normSq (𝓕 G (-t / (2 * Real.pi))) := by
    intro t
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hri := hi.re
  simp only [RCLike.re_to_complex] at hri
  refine ⟨hri.congr (Filter.Eventually.of_forall he), ?_⟩
  have hz := congrArg Complex.re (angular_krein_pairing G a b hG hs H hHc hH hFH hHs)
  have hre := (integral_re hi).symm
  simp only [RCLike.re_to_complex] at hre
  rw [hre] at hz
  simpa only [he, Complex.zero_re] using hz

theorem fourier_reflection (G : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => G (-x)) ξ = 𝓕 G (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_neg_eq_self (fun x : ℝ =>
    Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) • G (-x))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [neg_neg]
  congr 2
  push_cast
  ring

/-- A genuine certificate with support outside the packet-difference window
implies a margin for the actual canonical zero quadratic. The factor, mass,
integrability, reflection and correction-pairing obligations are discharged. -/
theorem zero_quadratic_margin_from_genuine_certificate
    (g : WeilCompactSmoothGV1) (r a m : ℝ) (hr0 : 0 ≤ r)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g)
    (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hHs : ∀ u : ℝ, |u| < 2 * r → H u = 0)
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m) +
      (𝓕 H (-t / (2 * Real.pi))).re) :
    m * energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨χ, hc, hs, hi, hf⟩ :=
    actual_packet_fourier_factor g (a - r) (a + r) (by linarith) hw hm
  let χn : ℝ → ℂ := fun x => χ (-x)
  let ρ : ℝ → ℝ := fun t => Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
    Complex.normSq (𝓕 χn (-t / (2 * Real.pi)))
  let C : ℝ → ℝ := fun t => (𝓕 H (-t / (2 * Real.pi))).re
  have hχs : ∀ y, χ y ≠ 0 → y ∈ Ioo (a - r) (a + r) :=
    AEGIS.RHKreinFactorV13.ne_zero_mem_Ioo χ hc.continuous (a - r) (a + r) hs
  have hχns : ∀ y, χn y ≠ 0 → y ∈ Ioo (-(a + r)) (-(a - r)) := by
    intro y hy
    have h := hχs (-y) hy
    constructor <;> linarith [h.1, h.2]
  have hχni : Integrable χn := hi.comp_neg
  have hfirst := real_angular_krein_pairing χ (a - r) (a + r) hi hχs
    H hHc hH hFH (fun u hu => hHs u (by linarith))
  have hsecond := real_angular_krein_pairing χn (-(a + r)) (-(a - r)) hχni hχns
    H hHc hH hFH (fun u hu => hHs u (by linarith))
  have hρ : ∀ t : ℝ, 0 ≤ ρ t := by
    intro t
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t := by
    intro t
    unfold criticalSpectralMass
    rw [hf t, hf (-t)]
    dsimp [ρ, χn]
    rw [fourier_reflection]
    have he : -(-t / (2 * Real.pi)) = -(-t) / (2 * Real.pi) := by ring
    rw [he]
    ring
  have hsplit : ∀ t : ℝ, C t * ρ t =
      (𝓕 H (-t / (2 * Real.pi))).re * Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
      (𝓕 H (-t / (2 * Real.pi))).re * Complex.normSq (𝓕 χn (-t / (2 * Real.pi))) := by
    intro t
    dsimp [C, ρ]
    ring
  have hCi : Integrable (fun t : ℝ => C t * ρ t) :=
    (hfirst.1.add hsecond.1).congr (Filter.Eventually.of_forall fun t => by
      change (𝓕 H (-t / (2 * Real.pi))).re *
          Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
        (𝓕 H (-t / (2 * Real.pi))).re *
          Complex.normSq (𝓕 χn (-t / (2 * Real.pi))) = C t * ρ t
      exact (hsplit t).symm)
  have hCz : (∫ t : ℝ, C t * ρ t) = 0 := by
    simp_rw [hsplit]
    rw [integral_add hfirst.1 hsecond.1, hfirst.2, hsecond.2, add_zero]
  exact zero_quadratic_margin_of_weighted_certificate g r a m hw hr hm
    ρ C hρ hmass hCi hCz hcert

end AEGIS.RHKreinGenuineCertificateV1

#print axioms AEGIS.RHKreinGenuineCertificateV1.real_angular_krein_pairing
#print axioms AEGIS.RHKreinGenuineCertificateV1.fourier_reflection
#print axioms AEGIS.RHKreinGenuineCertificateV1.zero_quadratic_margin_from_genuine_certificate
