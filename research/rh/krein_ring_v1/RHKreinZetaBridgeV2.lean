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

import RHKreinZetaBridgeV1

/-!
AEGIS Ω — Krein bridge beyond log 3 (v2).

`certificate_generic`: the V1 argument with the symbol `S` abstracted (its integrability against `Nr` and
the identity `Re Σ_ρ Z_ρ = (1/2π)∫ S·Nr` become hypotheses).

`Scert3` adds the prime `3` to the symbol: `S₃(t) = Re ψ(1/4+it/2) − log π − Σ_{p∈{2,3}} log p·2p^{-1/2}cos(t log p)`.
`zero_quadratic_eq_scert3`: for log-support width `2r < log 4` the zero quadratic is `(1/2π)∫ S₃·Nr`
(every prime power `m ≥ 4` pairs to zero). `certificate3_zero_quadratic_nonneg`: a certificate with symbol
`S₃` and window `L ≤ log 4` gives `Re Σ_ρ Z_ρ ≥ 0` on width `< L`. Not RH.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
open scoped ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace AEGIS.RHKreinZetaBridgeV2

open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilCriticalLinePrimeV1
open AEGIS.RHKreinZetaBridgeV1

theorem certificate_generic (S : ℝ → ℝ) (L m : ℝ)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (S t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a)
    (hSint : Integrable (fun t => S t * Nr g t))
    (hZ : (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, S t * Nr g t) :
    m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
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
  rw [hZ]
  exact key


/-- Symbol with primes `2` and `3`. -/
def Scert3 (t : ℝ) : ℝ :=
  Psi t - Real.log Real.pi -
    Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)) * Real.cos (t * Real.log 2) -
    Real.log 3 * (2 * Real.exp (-(Real.log 3) / 2)) * Real.cos (t * Real.log 3)

theorem scert3Nr_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t => Scert3 t * Nr g t) := by
  have hA := (psiNr_integrable g).sub
    ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
  have hB := (cosNr_integrable g (Real.log 2)).const_mul
    (Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)))
  have hC := (cosNr_integrable g (Real.log 3)).const_mul
    (Real.log 3 * (2 * Real.exp (-(Real.log 3) / 2)))
  refine ((hA.sub hB).sub hC).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, Scert3]; ring

theorem zero_quadratic_eq_scert3 (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (hr4 : 2 * r < Real.log 4) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, Scert3 t * Nr g t := by
  rw [zero_quadratic_krein_form_v1 g hm]
  have hts : ∀ n : ℕ, n ∉ ({1, 2} : Finset ℕ) →
      ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, ((2 * Real.exp (-(Real.log ((n + 1 : ℕ) : ℝ)) / 2) *
              Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * criticalDensityV1 g t) = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 0 := by omega
      subst this; simp
    · rw [prime_int, cos_pair_zero g r a hw]
      · simp
      · have h4 : (4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          have : (4 : ℕ) ≤ n + 1 := by omega
          exact_mod_cast this
        have := Real.log_le_log (by norm_num) h4
        linarith
  have hae := arch_even g
  simp only [Psi] at hae
  rw [tsum_eq_sum hts, Finset.sum_pair (by norm_num), prime_int, prime_int, hae]
  have hΛ2 : (ArithmeticFunction.vonMangoldt (1 + 1) : ℝ) = Real.log 2 := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hΛ3 : (ArithmeticFunction.vonMangoldt (2 + 1) : ℝ) = Real.log 3 := by
    rw [show (2 + 1 : ℕ) = 3 from rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    norm_num
  have h2 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  have h3 : ((2 + 1 : ℕ) : ℝ) = 3 := by norm_num
  rw [hΛ2, hΛ3, h2, h3]
  have hA : Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g t) := by
    have := (psiNr_integrable g).sub
      ((Nr_integrable g).const_mul (Real.eulerMascheroniConstant + Real.log Real.pi))
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; ring
  have hB := (cosNr_integrable g (Real.log 2)).const_mul
    (Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)))
  have hC := (cosNr_integrable g (Real.log 3)).const_mul
    (Real.log 3 * (2 * Real.exp (-(Real.log 3) / 2)))
  have hS : (∫ t : ℝ, Scert3 t * Nr g t) =
      (∫ t : ℝ, (Psi t - Real.log Real.pi) * Nr g t) -
        Real.log 2 * ((2 * Real.exp (-(Real.log 2) / 2)) *
          ∫ t : ℝ, Real.cos (t * Real.log 2) * Nr g t) -
        Real.log 3 * ((2 * Real.exp (-(Real.log 3) / 2)) *
          ∫ t : ℝ, Real.cos (t * Real.log 3) * Nr g t) := by
    have e2 : Real.log 2 * ((2 * Real.exp (-(Real.log 2) / 2)) *
        ∫ t : ℝ, Real.cos (t * Real.log 2) * Nr g t) =
        ∫ t : ℝ, Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)) *
          (Real.cos (t * Real.log 2) * Nr g t) := by
      rw [integral_const_mul]; ring
    have e3 : Real.log 3 * ((2 * Real.exp (-(Real.log 3) / 2)) *
        ∫ t : ℝ, Real.cos (t * Real.log 3) * Nr g t) =
        ∫ t : ℝ, Real.log 3 * (2 * Real.exp (-(Real.log 3) / 2)) *
          (Real.cos (t * Real.log 3) * Nr g t) := by
      rw [integral_const_mul]; ring
    have hAB : Integrable (fun t => (Psi t - Real.log Real.pi) * Nr g t -
        Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)) * (Real.cos (t * Real.log 2) * Nr g t)) :=
      hA.sub hB
    rw [e2, e3, ← integral_sub hA hB, ← integral_sub hAB hC]
    congr 1; funext t; simp only [Scert3, Psi]; ring
  have hc : ∀ X Y Z : ℝ, ((1 / (2 * (Real.pi : ℂ))) * (X : ℂ) -
      (((Real.log 2 : ℝ) : ℂ) * ((1 / (2 * (Real.pi : ℂ))) * (Y : ℂ)) +
        ((Real.log 3 : ℝ) : ℂ) * ((1 / (2 * (Real.pi : ℂ))) * (Z : ℂ)))) =
      (((1 / (2 * Real.pi)) * X - Real.log 2 * ((1 / (2 * Real.pi)) * Y) -
        Real.log 3 * ((1 / (2 * Real.pi)) * Z) : ℝ) : ℂ) := by
    intro X Y Z; push_cast; ring
  rw [hc, Complex.ofReal_re, hS]
  simp only [Psi]
  ring

/-- **Certificate with primes `2, 3` ⇒ nonnegative zeta zero quadratic on width `< L ≤ log 4`.** -/
theorem certificate3_zero_quadratic_nonneg (L m : ℝ) (hm0 : 0 ≤ m) (hL4 : L ≤ Real.log 4)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (Scert3 t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < L) (hw : HalfWidthAt g r a) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have h := certificate_generic Scert3 L m H hHc hHi hFH hHs d j hcert g hmom r a hr hrL hw
    (scert3Nr_integrable g) (zero_quadratic_eq_scert3 g hmom r a hw (by linarith))
  have hN : 0 ≤ ∫ t : ℝ, Nr g t := integral_nonneg (Nr_nonneg g)
  have : 0 ≤ m * ((1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t) := by positivity
  linarith

end AEGIS.RHKreinZetaBridgeV2

#print axioms AEGIS.RHKreinZetaBridgeV2.certificate_generic
#print axioms AEGIS.RHKreinZetaBridgeV2.zero_quadratic_eq_scert3
#print axioms AEGIS.RHKreinZetaBridgeV2.certificate3_zero_quadratic_nonneg
