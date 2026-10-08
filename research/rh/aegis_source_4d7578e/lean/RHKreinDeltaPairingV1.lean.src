import Mathlib

/-!
AEGIS Ω — Krein pairing for the boundary columns ξ^j·e^{±2πiξL} of the dual certificate.

`RHKreinPairingV13.krein_pairing` covers genuine functions `H` vanishing on `|u| < L`. The certificate in
`RH_STATUS.md` also uses the distributional columns `δ^{(j)}(|u| − L)`, whose Fourier transforms are
`ξ^j cos(ξL)` / `ξ^j sin(ξL)`. This module proves that they pair to zero as well:

* `cross_support`: the cross-correlation `G₁ ⋆ G̃₂` vanishes on `|x| ≥ b − a` when both factors vanish outside `(a, b)`.
* `fourier_cross`: `𝓕(G₁ ⋆ G̃₂) = 𝓕G₁ · conj 𝓕G₂` (Mathlib's convolution theorem).
* `cross_pairing_zero`: for `L ≥ b − a`, `∫ 𝓕G₁(ξ)·conj(𝓕G₂(ξ))·e^{2πiξL} dξ = 0` (Fourier inversion at `x = −L`).
* `delta_pairing_zero`: with `G₁ = G^{(j₁)}`, `G₂ = G^{(j₂)}` (Mathlib's `fourier_iteratedDeriv`), the column
  `ξ^{j₁+j₂} e^{2πiξL} |𝓕G(ξ)|²` integrates to zero.

Not RH.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Convolution
open scoped ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace AEGIS.RHKreinDeltaPairingV1

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

/-- Cross-correlation `G₁ ⋆ G̃₂`, `G̃₂(x) = conj G₂(−x)`. -/
def cross (G₁ G₂ : ℝ → ℂ) : ℝ → ℂ :=
  G₁ ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (starRingEnd ℂ) (G₂ (-x)))

theorem tilde_integrable (G : ℝ → ℂ) (hG : Integrable G) :
    Integrable (fun x => (starRingEnd ℂ) (G (-x))) := by
  have h := (Complex.conjLIE.toContinuousLinearMap).integrable_comp hG.comp_neg
  simpa using h

theorem fourier_cross (G₁ G₂ : ℝ → ℂ) (h₁ : Integrable G₁) (h₂ : Integrable G₂) (ξ : ℝ) :
    𝓕 (cross G₁ G₂) ξ = 𝓕 G₁ ξ * (starRingEnd ℂ) (𝓕 G₂ ξ) := by
  unfold cross
  rw [Real.fourier_mul_convolution_eq h₁ (tilde_integrable G₂ h₂), fourier_conj_neg]

theorem cross_support (G₁ G₂ : ℝ → ℂ) (a b : ℝ)
    (hs₁ : ∀ y, G₁ y ≠ 0 → y ∈ Set.Ioo a b) (hs₂ : ∀ y, G₂ y ≠ 0 → y ∈ Set.Ioo a b) :
    ∀ x, cross G₁ G₂ x ≠ 0 → |x| < b - a := by
  intro x hx
  by_contra hge
  apply hx
  have hz : ∀ t, G₁ t * (starRingEnd ℂ) (G₂ (t - x)) = 0 := by
    intro t
    by_cases h1 : G₁ t = 0
    · rw [h1, zero_mul]
    · by_cases h2 : G₂ (t - x) = 0
      · rw [h2, map_zero, mul_zero]
      · exfalso
        have m1 := hs₁ t h1
        have m2 := hs₂ _ h2
        apply hge
        rw [abs_lt]
        constructor <;> linarith [m1.1, m1.2, m2.1, m2.2]
  unfold cross
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', neg_sub]
  simp [hz]

/-- **Boundary-column pairing.** If `G₁, G₂` are integrable, vanish outside `(a, b)`, their
cross-correlation is continuous and its Fourier transform integrable, then for every `L ≥ b − a`
`∫ 𝓕G₁(ξ)·conj(𝓕G₂(ξ))·e^{2πiξL} dξ = 0`. -/
theorem cross_pairing_zero (G₁ G₂ : ℝ → ℂ) (a b L : ℝ) (h₁ : Integrable G₁) (h₂ : Integrable G₂)
    (hs₁ : ∀ y, G₁ y ≠ 0 → y ∈ Set.Ioo a b) (hs₂ : ∀ y, G₂ y ≠ 0 → y ∈ Set.Ioo a b)
    (hc : Continuous (cross G₁ G₂)) (hF : Integrable (𝓕 (cross G₁ G₂))) (hL : b - a ≤ L) :
    ∫ ξ, 𝓕 G₁ ξ * (starRingEnd ℂ) (𝓕 G₂ ξ) *
        Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I) = 0 := by
  have hX : Integrable (cross G₁ G₂) :=
    h₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (tilde_integrable G₂ h₂)
  have hinv := hc.fourierInv_fourier_eq hX hF
  have hval : cross G₁ G₂ L = 0 := by
    by_contra hne
    have h1 := cross_support G₁ G₂ a b hs₁ hs₂ L hne
    have h2 := le_abs_self L
    linarith
  have h := congrFun hinv L
  rw [hval, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  rw [← h]
  congr 1
  funext ξ
  rw [fourier_cross G₁ G₂ h₁ h₂ ξ, smul_eq_mul]
  ring_nf

/-- `‖𝓕 f ξ‖ ≤ ∫ ‖f‖`. -/
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp_rw [Circle.norm_smul]
  exact le_rfl

section smooth
variable (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hts : tsupport G ⊆ Set.Ioo a b)
include hG hts

theorem hasCompactSupport_of_ts : HasCompactSupport G :=
  (isCompact_Icc (a := a) (b := b)).of_isClosed_subset (isClosed_tsupport G)
    (hts.trans Set.Ioo_subset_Icc_self)

theorem iteratedDeriv_support_sub (j : ℕ) :
    Function.support (iteratedDeriv j G) ⊆ tsupport G := by
  intro y hy
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) j
  intro h
  apply hy
  rw [iteratedDeriv_eq_iteratedFDeriv, h]
  rfl

theorem iteratedDeriv_vanish (j : ℕ) :
    ∀ y, iteratedDeriv j G y ≠ 0 → y ∈ Set.Ioo a b :=
  fun _y hy => hts (iteratedDeriv_support_sub G hG a b hts j hy)

theorem iteratedDeriv_contDiff (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv j

theorem iteratedDeriv_hasCompactSupport (j : ℕ) : HasCompactSupport (iteratedDeriv j G) :=
  (hasCompactSupport_of_ts G hG a b hts).mono' (iteratedDeriv_support_sub G hG a b hts j)

theorem iteratedDeriv_integrable (j : ℕ) : Integrable (iteratedDeriv j G) :=
  (iteratedDeriv_contDiff G hG a b hts j).continuous.integrable_of_hasCompactSupport
    (iteratedDeriv_hasCompactSupport G hG a b hts j)

/-- **Boundary columns `δ^{(j)}` pair to zero.** For smooth `G` with `tsupport G ⊆ (a, b)` and `L ≥ b − a`,
`∫ ((2πiξ)^{j₁} 𝓕G(ξ)) · conj((2πiξ)^{j₂} 𝓕G(ξ)) · e^{2πiξL} dξ = 0`. -/
theorem delta_pairing_zero (j₁ j₂ : ℕ) (L : ℝ) (hL : b - a ≤ L) :
    ∫ ξ : ℝ, ((2 * Real.pi * Complex.I * ξ) ^ j₁ * 𝓕 G ξ) *
        (starRingEnd ℂ) ((2 * Real.pi * Complex.I * ξ) ^ j₂ * 𝓕 G ξ) *
        Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I) = 0 := by
  have hi1 := iteratedDeriv_integrable G hG a b hts j₁
  have hi2 := iteratedDeriv_integrable G hG a b hts j₂
  have hc : Continuous (cross (iteratedDeriv j₁ G) (iteratedDeriv j₂ G)) := by
    unfold cross
    exact (iteratedDeriv_hasCompactSupport G hG a b hts j₁).continuous_convolution_left _
      (iteratedDeriv_contDiff G hG a b hts j₁).continuous
      (tilde_integrable _ hi2).locallyIntegrable
  let S1 := (iteratedDeriv_hasCompactSupport G hG a b hts j₁).toSchwartzMap
    (iteratedDeriv_contDiff G hG a b hts j₁)
  let S2 := (iteratedDeriv_hasCompactSupport G hG a b hts j₂).toSchwartzMap
    (iteratedDeriv_contDiff G hG a b hts j₂)
  have hF1 : Integrable (𝓕 (iteratedDeriv j₁ G)) := by
    have h0 := (𝓕 S1).integrable (μ := volume)
    exact h0
  have hF2c : Continuous (𝓕 (iteratedDeriv j₂ G)) := by
    have h0 := (𝓕 S2).continuous
    exact h0
  have hF : Integrable (𝓕 (cross (iteratedDeriv j₁ G) (iteratedDeriv j₂ G))) := by
    have heq : 𝓕 (cross (iteratedDeriv j₁ G) (iteratedDeriv j₂ G)) =
        fun ξ => (starRingEnd ℂ) (𝓕 (iteratedDeriv j₂ G) ξ) * 𝓕 (iteratedDeriv j₁ G) ξ := by
      funext ξ; rw [fourier_cross _ _ hi1 hi2, mul_comm]
    rw [heq]
    refine hF1.bdd_mul (c := ∫ x, ‖iteratedDeriv j₂ G x‖) ?_ ?_
    · exact (Complex.continuous_conj.comp hF2c).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [Complex.norm_conj]; exact norm_fourier_le _ ξ
  have h := cross_pairing_zero (iteratedDeriv j₁ G) (iteratedDeriv j₂ G) a b L hi1 hi2
    (iteratedDeriv_vanish G hG a b hts j₁) (iteratedDeriv_vanish G hG a b hts j₂) hc hF hL
  have hall : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n G) :=
    fun n _ => iteratedDeriv_integrable G hG a b hts n
  rw [Real.fourier_iteratedDeriv (N := ⊤) hG hall le_top,
    Real.fourier_iteratedDeriv (N := ⊤) hG hall le_top] at h
  simpa [smul_eq_mul] using h

end smooth

end AEGIS.RHKreinDeltaPairingV1

#print axioms AEGIS.RHKreinDeltaPairingV1.cross_pairing_zero
#print axioms AEGIS.RHKreinDeltaPairingV1.iteratedDeriv_integrable
#print axioms AEGIS.RHKreinDeltaPairingV1.delta_pairing_zero
