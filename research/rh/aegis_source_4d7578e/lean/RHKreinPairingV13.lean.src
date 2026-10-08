import Mathlib

/-!
AEGIS Ω — the Krein pairing for the Fourier-side dual certificate, V13.

The certificate in `RH_STATUS.md` adds `Ĥ(ξ)` to the weighted symbol, with `H` supported outside the
window `|u| < L`. This module proves that such a term pairs to zero against `|Ĝ₁|²`, where `G₁` is supported
in an interval of length `L`:

* `self_adj`: `∫ 𝓕f·g = ∫ f·𝓕g` (Mathlib's `VectorFourier.integral_fourierIntegral_smul_eq_flip`).
* `fourier_fourier`: `𝓕(𝓕H)(x) = H(−x)` from Fourier inversion.
* `fourier_conj_neg`, `fourier_autoc`: for `A = G ⋆ G̃`, `𝓕A = |𝓕G|²` (Mathlib's convolution theorem).
* `autoc_support`: `A` vanishes on `|x| ≥ b − a` when `G` vanishes outside `(a, b)`.
* `pairing_zero`, `krein_pairing`: `∫ |𝓕G|²·𝓕H = ∫ A(x)·H(−x) dx = 0`, since the supports are disjoint.

With `RHKreinFactorV13` (support of `g₁`) this gives the pairing step of the certificate. Not RH.
AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinPairingV13

theorem self_adj (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := volume) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf hg
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral, smul_eq_mul] using h

theorem fourier_fourier (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H)
    (hFH : Integrable (𝓕 H)) (x : ℝ) : 𝓕 (𝓕 H) x = H (-x) := by
  have hinv := hHc.fourierInv_fourier_eq hH hFH
  have h := Real.fourierInv_eq_fourier_neg (𝓕 H) (-x)
  rw [neg_neg] at h
  rw [← h, hinv]

theorem pairing_zero (A H : ℝ → ℂ) (L : ℝ) (hA : Integrable A) (hHc : Continuous H)
    (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hAs : ∀ x, A x ≠ 0 → |x| < L) (hHs : ∀ u, |u| < L → H u = 0) :
    ∫ ξ, 𝓕 A ξ * 𝓕 H ξ = 0 := by
  rw [self_adj A (𝓕 H) hA hFH]
  simp_rw [fourier_fourier H hHc hH hFH]
  have hz : ∀ x, A x * H (-x) = 0 := by
    intro x
    by_cases h : A x = 0
    · simp [h]
    · rw [hHs (-x) (by rw [abs_neg]; exact hAs x h), mul_zero]
  simp [hz]

theorem fourier_conj_neg (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => (starRingEnd ℂ) (f (-x))) ξ = (starRingEnd ℂ) (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj, ← integral_neg_eq_self]
  congr 1
  funext x
  simp only [smul_eq_mul, map_mul, neg_neg, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

open Convolution in
/-- The autocorrelation `A = G ⋆ G̃`, `G̃(x) = conj G(−x)`. -/
noncomputable def autoc (G : ℝ → ℂ) : ℝ → ℂ :=
  G ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (starRingEnd ℂ) (G (-x)))

theorem fourier_autoc (G : ℝ → ℂ) (hG : Integrable G) (ξ : ℝ) :
    𝓕 (autoc G) ξ = ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) := by
  have hGt : Integrable (fun x => (starRingEnd ℂ) (G (-x))) := by
    have h := (Complex.conjLIE.toContinuousLinearMap).integrable_comp hG.comp_neg
    simpa using h
  unfold autoc
  rw [Real.fourier_mul_convolution_eq hG hGt, fourier_conj_neg, Complex.mul_conj]

open Convolution in
theorem autoc_support (G : ℝ → ℂ) (a b : ℝ) (hsupp : ∀ y, G y ≠ 0 → y ∈ Set.Ioo a b) :
    ∀ x, autoc G x ≠ 0 → |x| < b - a := by
  intro x hx
  by_contra hge
  apply hx
  have hz : ∀ t, G t * (starRingEnd ℂ) (G (t - x)) = 0 := by
    intro t
    by_cases h1 : G t = 0
    · rw [h1, zero_mul]
    · by_cases h2 : G (t - x) = 0
      · rw [h2, map_zero, mul_zero]
      · exfalso
        have m1 := hsupp t h1
        have m2 := hsupp _ h2
        apply hge
        rw [abs_lt]
        constructor <;> linarith [m1.1, m1.2, m2.1, m2.2]
  unfold autoc
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', neg_sub]
  simp [hz]

/-- **Krein pairing.** If `G` is integrable and vanishes outside `(a, b)`, and `H` is continuous and
integrable with integrable Fourier transform and vanishes on `|u| < b − a`, then
`∫ |𝓕G(ξ)|²·𝓕H(ξ) dξ = 0`. So a dual-certificate term `Ĥ` supported outside the window costs nothing. -/
theorem krein_pairing (G : ℝ → ℂ) (a b : ℝ) (hG : Integrable G)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ Set.Ioo a b)
    (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hHs : ∀ u, |u| < b - a → H u = 0) :
    ∫ ξ, ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) * 𝓕 H ξ = 0 := by
  have hGt : Integrable (fun x => (starRingEnd ℂ) (G (-x))) := by
    have h := (Complex.conjLIE.toContinuousLinearMap).integrable_comp hG.comp_neg
    simpa using h
  have hA : Integrable (autoc G) := hG.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hGt
  simp_rw [← fourier_autoc G hG]
  exact pairing_zero (autoc G) H (b - a) hA hHc hH hFH (autoc_support G a b hsupp) hHs

end AEGIS.RHKreinPairingV13

#print axioms AEGIS.RHKreinPairingV13.krein_pairing
