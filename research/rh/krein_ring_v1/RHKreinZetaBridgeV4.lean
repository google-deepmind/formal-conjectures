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

import RHKreinZetaBridgeV3

/-!
# Krein certificate with slack (v4)

`certificate_raw`: the V2 argument without the zero-quadratic identity, for any symbol `S`:
`m · (1/2π)∫ Nr ≤ (1/2π)∫ S·Nr`.

`certificate_slack`: if `W (S_M − m) + Ĥ + δ-terms + W·s ≥ 0` pointwise, with `s` bounded and
measurable (the slack), then for every moment-zero packet of width `2r < L ≤ log (M+1)`

  `m · N(g) ≤ Re Σ_ρ Z_ρ(A_g) + K_s(g)`,   `N(g) = (1/2π)∫ Nr`,   `K_s(g) = (1/2π)∫ s·Nr`.

This is the complement step of the Feshbach certificates: the slack is paid by the low block.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinZetaBridgeV4

open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilCriticalLinePrimeV1
open AEGIS.RHKreinZetaBridgeV1
open AEGIS.RHKreinZetaBridgeV3

theorem certificate_raw (S : ℝ → ℝ) (L m : ℝ)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (S t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a)
    (hSint : Integrable (fun t => S t * Nr g t)) :
    m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, S t * Nr g t := by
  obtain ⟨chi, hc, hs, hNr⟩ := Nr_factor g r a hr hw hmom
  set ε := (L - 2 * r) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hts : tsupport chi ⊆ Set.Ioo (-a - r - ε) (-a + r + ε) :=
    hs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hba : (-a + r + ε) - (-a - r - ε) = L := by rw [hε]; ring
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hNrν : ∀ ν : ℝ, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν) = Nr g (2 * Real.pi * ν) := by
    intro ν; rw [hNr, two_pi_div]
  have hW : Integrable (fun ν => Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) := by
    refine ((Nr_integrable g).comp_mul_left' h2pi).congr
      (Filter.Eventually.of_forall fun ν => ?_)
    simp only [hNrν]
  have hWS : Integrable (fun ν => Wt (2 * Real.pi * ν) * S (2 * Real.pi * ν) *
      Complex.normSq (𝓕 chi ν)) := by
    refine (hSint.comp_mul_left' h2pi).congr
      (Filter.Eventually.of_forall fun ν => ?_)
    show S (2 * Real.pi * ν) * Nr g (2 * Real.pi * ν) = _
    rw [← hNrν]; ring
  have hcert' : ∀ ξ : ℝ, 0 ≤ Wt (2 * Real.pi * ξ) * (S (2 * Real.pi * ξ) - m) +
      (∑ i, 𝓕 (H i) ξ).re + ∑ l, 2 * (d l * ((2 * Real.pi * I * ξ) ^ j l *
        Complex.exp (↑(2 * Real.pi * ξ * L) * I))).re := by
    intro ξ
    have h := hcert (2 * Real.pi * ξ)
    rw [two_pi_div] at h
    have e1 : ∀ l, (I * (((2 * Real.pi * ξ : ℝ)) : ℂ)) ^ j l = (2 * (Real.pi : ℂ) * I * ξ) ^ j l := by
      intro l; push_cast; ring_nf
    simp only [e1] at h
    exact h
  have hHs' : ∀ i u, |u| < (-a + r + ε) - (-a - r - ε) → H i u = 0 := by
    rw [hba]; exact hHs
  have key := AEGIS.RHKreinCertificateV1.certificate_lower_bound chi hc _ _ hts L hba.le
    (fun ν => Wt (2 * Real.pi * ν)) (fun ν => S (2 * Real.pi * ν)) m H hHc hHi hFH hHs' d j
    hWS hW hcert'
  have e2 : (∫ ν, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, Nr g t := by
    rw [← integral_two_pi (Nr g)]; congr 1; funext ν; exact hNrν ν
  have e3 : (∫ ν, Wt (2 * Real.pi * ν) * S (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, S t * Nr g t := by
    rw [← integral_two_pi (fun t => S t * Nr g t)]; congr 1; funext ν
    show _ = S (2 * Real.pi * ν) * Nr g (2 * Real.pi * ν)
    rw [← hNrν]; ring
  rw [e2, e3] at key
  exact key

/-- **Krein certificate with slack.** -/
theorem certificate_slack (M : ℕ) (L m : ℝ) (hLM : L ≤ Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a) :
    m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re +
        (1 / (2 * Real.pi)) * ∫ t : ℝ, s t * Nr g t := by
  have hsNr : Integrable (fun t => s t * Nr g t) := by
    refine (Nr_integrable g).bdd_mul (c := B) hsm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hsB t
  have hSint : Integrable (fun t => (ScertM M t + s t) * Nr g t) := by
    refine ((scertMNr_integrable M g).add hsNr).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]; ring
  have hcert' : ∀ t : ℝ, 0 ≤ Wt t * ((ScertM M t + s t) - m) +
      (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re := by
    intro t; have := hcert t; linarith
  have h := certificate_raw (fun t => ScertM M t + s t) L m H hHc hHi hFH hHs d j hcert'
    g hmom r a hr hrL hw hSint
  have hsplit : (∫ t : ℝ, (ScertM M t + s t) * Nr g t) =
      (∫ t : ℝ, ScertM M t * Nr g t) + ∫ t : ℝ, s t * Nr g t := by
    rw [← integral_add (scertMNr_integrable M g) hsNr]
    congr 1; funext t; ring
  rw [hsplit, mul_add, ← zero_quadratic_eq_scertM g hmom r a hw M (by linarith)] at h
  exact h

end AEGIS.RHKreinZetaBridgeV4

#print axioms AEGIS.RHKreinZetaBridgeV4.certificate_slack
