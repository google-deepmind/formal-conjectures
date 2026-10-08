import RHKreinPairingV13
import RHKreinDeltaPairingV1

/-!
AEGIS Ω — from a Krein dual certificate to a lower bound on the weighted form (v1).

The Arb certificates `KREIN_ARB_CERTIFICATE_L0.8/0.9.json` check, on the Fourier side, a pointwise inequality
`0 ≤ W(ξ)(S(ξ) − m) + Re Σᵢ 𝓕Hᵢ(ξ) + Σₗ 2·Re(dₗ (2πiξ)^{jₗ} e^{2πiξL})`, with hats `Hᵢ` vanishing on
`|u| < L` and boundary columns `δ^{(j)}`. This module proves that such an inequality forces

  `m · ∫ W |𝓕G|² ≤ ∫ W S |𝓕G|²`

for every smooth `G` with `tsupport G ⊆ (a, b)`, `b − a ≤ L`: the hats and the columns pair to zero
(`krein_pairing`, `delta_pairing_zero`), so only the `W(S − m)` part survives.

The certificate inequality is a hypothesis here; the Arb check is not formalized. Relating `W·S` to the
zeta zero quadratic (`zero_quadratic_krein_form_v1`, PR #693) is a separate step. Not RH.
AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCertificateV1

set_option linter.unusedSectionVars false

open AEGIS.RHKreinDeltaPairingV1 in
section
variable (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hts : tsupport G ⊆ Set.Ioo a b)
include hG hts

theorem integrable_G : Integrable G := by
  simpa using iteratedDeriv_integrable G hG a b hts 0

theorem vanish_G : ∀ y, G y ≠ 0 → y ∈ Set.Ioo a b := by
  simpa using iteratedDeriv_vanish G hG a b hts 0

theorem normSq_le (ξ : ℝ) : Complex.normSq (𝓕 G ξ) ≤ (∫ x, ‖G x‖) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_le G ξ) 2

theorem integrable_poly_fourier (j : ℕ) :
    Integrable (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) ^ j * 𝓕 G ξ) := by
  let S := (iteratedDeriv_hasCompactSupport G hG a b hts j).toSchwartzMap
    (iteratedDeriv_contDiff G hG a b hts j)
  have h0 : Integrable (𝓕 (iteratedDeriv j G)) := (𝓕 S).integrable (μ := volume)
  have hall : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n G) :=
    fun n _ => iteratedDeriv_integrable G hG a b hts n
  rw [Real.fourier_iteratedDeriv (N := ⊤) hG hall le_top] at h0
  exact h0

/-- A boundary column integrates to zero against `|𝓕G|²`. -/
theorem column_zero (j : ℕ) (L : ℝ) (hL : b - a ≤ L) :
    ∫ ξ : ℝ, ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) *
        ((2 * Real.pi * Complex.I * ξ) ^ j * Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I)) = 0 := by
  have h := delta_pairing_zero G hG a b hts j 0 L hL
  rw [← h]
  congr 1; funext ξ
  rw [← Complex.mul_conj]
  simp only [pow_zero, one_mul]
  ring

theorem column_integrable (j : ℕ) (L : ℝ) :
    Integrable (fun ξ : ℝ => ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) *
        ((2 * Real.pi * Complex.I * ξ) ^ j * Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I))) := by
  have hi := integrable_poly_fourier G hG a b hts j
  have heq : (fun ξ : ℝ => ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) *
        ((2 * Real.pi * Complex.I * ξ) ^ j * Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I))) =
      fun ξ => ((starRingEnd ℂ) (𝓕 G ξ) * Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I)) *
        ((2 * Real.pi * Complex.I * ξ) ^ j * 𝓕 G ξ) := by
    funext ξ; rw [← Complex.mul_conj]; ring
  rw [heq]
  refine hi.bdd_mul (c := ∫ x, ‖G x‖) ?_ ?_
  · let S0 := (iteratedDeriv_hasCompactSupport G hG a b hts 0).toSchwartzMap
      (iteratedDeriv_contDiff G hG a b hts 0)
    have hc : Continuous (𝓕 (iteratedDeriv 0 G)) := (𝓕 S0).continuous
    simp only [iteratedDeriv_zero] at hc
    exact ((Complex.continuous_conj.comp hc).mul (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact norm_fourier_le G ξ

theorem hat_integrable (H : ℝ → ℂ) (hFH : Integrable (𝓕 H)) :
    Integrable (fun ξ : ℝ => ((Complex.normSq (𝓕 G ξ) : ℝ) : ℂ) * 𝓕 H ξ) := by
  refine hFH.bdd_mul (c := (∫ x, ‖G x‖) ^ 2) ?_ ?_
  · let S0 := (iteratedDeriv_hasCompactSupport G hG a b hts 0).toSchwartzMap
      (iteratedDeriv_contDiff G hG a b hts 0)
    have hc : Continuous (𝓕 (iteratedDeriv 0 G)) := (𝓕 S0).continuous
    simp only [iteratedDeriv_zero] at hc
    exact (Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp hc)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
    exact normSq_le G hG a b hts ξ

/-- **Certificate ⇒ lower bound.** If the dual-certificate inequality holds pointwise, then
`m · ∫ W |𝓕G|² ≤ ∫ W S |𝓕G|²` for every smooth `G` supported in an interval of length `≤ L`. -/
theorem certificate_lower_bound (L : ℝ) (hL : b - a ≤ L) (W S : ℝ → ℝ) (m : ℝ)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < b - a → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hWS : Integrable fun ξ => W ξ * S ξ * Complex.normSq (𝓕 G ξ))
    (hW : Integrable fun ξ => W ξ * Complex.normSq (𝓕 G ξ))
    (hcert : ∀ ξ : ℝ, 0 ≤ W ξ * (S ξ - m) + (∑ i, 𝓕 (H i) ξ).re +
      ∑ l, 2 * (d l * ((2 * Real.pi * Complex.I * ξ) ^ j l *
        Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I))).re) :
    m * ∫ ξ, W ξ * Complex.normSq (𝓕 G ξ) ≤ ∫ ξ, W ξ * S ξ * Complex.normSq (𝓕 G ξ) := by
  set P : ℝ → ℝ := fun ξ => Complex.normSq (𝓕 G ξ) with hP
  set col : Fin k → ℝ → ℂ := fun l ξ =>
    (P ξ : ℂ) * ((2 * Real.pi * Complex.I * ξ) ^ j l *
      Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I)) with hcol
  set hat : Fin n → ℝ → ℂ := fun i ξ => (P ξ : ℂ) * 𝓕 (H i) ξ with hhat
  have hcolI : ∀ l, Integrable (col l) := fun l => column_integrable G hG a b hts (j l) L
  have hcol0 : ∀ l, ∫ ξ, col l ξ = 0 := fun l => column_zero G hG a b hts (j l) L hL
  have hhatI : ∀ i, Integrable (hat i) := fun i => hat_integrable G hG a b hts (H i) (hFH i)
  have hhat0 : ∀ i, ∫ ξ, hat i ξ = 0 := fun i =>
    AEGIS.RHKreinPairingV13.krein_pairing G a b (integrable_G G hG a b hts)
      (vanish_G G hG a b hts) (H i) (hHc i) (hHi i) (hFH i) (hHs i)
  -- the extra terms, as a real integrand
  set E : ℝ → ℝ := fun ξ => (∑ i, hat i ξ).re + ∑ l, 2 * (d l * col l ξ).re with hE
  have hEI : Integrable E := by
    refine (integrable_finsetSum _ fun i _ => hhatI i).re.add ?_
    exact integrable_finsetSum _ fun l _ => (((hcolI l).const_mul (d l)).re.const_mul 2)
  have hE0 : ∫ ξ, E ξ = 0 := by
    change ∫ ξ, ((∑ i, hat i ξ).re + ∑ l, 2 * (d l * col l ξ).re) = 0
    have hA : Integrable (fun ξ => (∑ i, hat i ξ).re) :=
      (integrable_finsetSum _ fun i _ => hhatI i).re
    have hB : Integrable (fun ξ => ∑ l, 2 * (d l * col l ξ).re) :=
      integrable_finsetSum _ fun l _ => (((hcolI l).const_mul (d l)).re.const_mul 2)
    rw [integral_add hA hB]
    have h1 : ∫ ξ, (∑ i, hat i ξ).re = 0 := by
      rw [show (fun ξ => (∑ i, hat i ξ).re) = fun ξ => RCLike.re (∑ i, hat i ξ) from rfl,
        integral_re (integrable_finsetSum _ fun i _ => hhatI i), integral_finsetSum _
          fun i _ => hhatI i]
      simp [hhat0]
    have h2 : ∫ ξ, ∑ l, 2 * (d l * col l ξ).re = 0 := by
      have hT : ∀ l ∈ (Finset.univ : Finset (Fin k)),
          Integrable (fun ξ => 2 * (d l * col l ξ).re) :=
        fun l _ => (((hcolI l).const_mul (d l)).re.const_mul 2)
      rw [integral_finsetSum _ hT]
      refine Finset.sum_eq_zero fun l _ => ?_
      have hre : ∫ ξ, (d l * col l ξ).re = 0 := by
        have := integral_re ((hcolI l).const_mul (d l))
        simp only [RCLike.re_to_complex] at this
        rw [this, integral_const_mul, hcol0 l]; simp
      rw [integral_const_mul, hre, mul_zero]
    rw [h1, h2, add_zero]
  -- pointwise: P·(certificate) = W S P − m W P + E
  have hpt : ∀ ξ, 0 ≤ W ξ * S ξ * P ξ - m * (W ξ * P ξ) + E ξ := by
    intro ξ
    have hPn : 0 ≤ P ξ := Complex.normSq_nonneg _
    have h := mul_nonneg hPn (hcert ξ)
    have hsum1 : (∑ i, hat i ξ).re = P ξ * (∑ i, 𝓕 (H i) ξ).re := by
      simp only [hhat, ← Finset.mul_sum, Complex.re_ofReal_mul]
    have hsum2 : ∑ l, 2 * (d l * col l ξ).re = P ξ * ∑ l, 2 * (d l * ((2 * Real.pi * Complex.I * ξ) ^ j l *
        Complex.exp (↑(2 * Real.pi * ξ * L) * Complex.I))).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hcol, mul_left_comm (d l) (P ξ : ℂ), Complex.re_ofReal_mul]
      ring
    simp only [hE, hsum1, hsum2]
    nlinarith [h]
  have hint : 0 ≤ ∫ ξ, (W ξ * S ξ * P ξ - m * (W ξ * P ξ) + E ξ) :=
    integral_nonneg hpt
  have hd : Integrable (fun ξ => W ξ * S ξ * P ξ - m * (W ξ * P ξ)) := hWS.sub (hW.const_mul m)
  have hmP : Integrable (fun ξ => m * (W ξ * P ξ)) := hW.const_mul m
  rw [integral_add hd hEI, hE0, add_zero, integral_sub hWS hmP, integral_const_mul] at hint
  linarith
end

end AEGIS.RHKreinCertificateV1

#print axioms AEGIS.RHKreinCertificateV1.certificate_lower_bound
