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

import RHKreinPrimeSymbolV1

/-!
# Transfer of a weighted Krein certificate to the actual Weil form

The pointwise certificate, mass factorization and correction pairing remain
explicit hypotheses. Integrability of the actual symbol and packet energy
is discharged by the repository identities. The conclusion is about the
actual arithmetic form, with no shadow quadratic form.
-/

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCertificateTransferV1

open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilDisjointEnergyV2

theorem symbol_mass_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t : ℝ => symbol t * criticalSpectralMass g t) := by
  refine ((archSymbol_mass_integrable g).sub
    ((cosine_mass_integrable g (Real.log 2)).const_mul
      (Real.sqrt 2 * Real.log 2))).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [symbol, Pi.sub_apply]
  ring

/-- An integrable zero-cost correction and a pointwise weighted certificate
imply a quantitative bound for the actual finite-window Weil arithmetic form. -/
theorem actual_margin_of_weighted_certificate
    (g : WeilCompactSmoothGV1) (r a m : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (ρ C : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0 ≤ ρ t)
    (hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t)
    (hCint : Integrable (fun t : ℝ => C t * ρ t))
    (hCzero : (∫ t : ℝ, C t * ρ t) = 0)
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m) + C t) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -m * energy g.1 := by
  have hS := symbol_mass_integrable g
  have hM := (criticalSpectralMass_integrable g).const_mul m
  have hD : Integrable (fun t : ℝ =>
      symbol t * criticalSpectralMass g t - m * criticalSpectralMass g t) := hS.sub hM
  have hnonneg : 0 ≤ ∫ t : ℝ,
      (symbol t * criticalSpectralMass g t - m * criticalSpectralMass g t) +
        C t * ρ t := by
    apply integral_nonneg
    intro t
    calc
      0 ≤ ((t ^ 2 + 1 / 4) ^ 2 * (symbol t - m) + C t) * ρ t :=
        mul_nonneg (hcert t) (hρ t)
      _ = _ := by
        dsimp only
        rw [hmass]
        ring
  rw [integral_add hD hCint, hCzero, add_zero,
    integral_sub hS hM, integral_const_mul] at hnonneg
  rw [actual_arithmetic_real_eq_symbol_integral g r a hw hr, energy_eq_mass_integral]
  have hK : 0 ≤ (1 / (4 * Real.pi) : ℝ) := by positivity
  have hbound := mul_nonneg hK hnonneg
  nlinarith

/-- The same certificate transfers to the actual canonical zero quadratic
when the two repository moments vanish. -/
theorem zero_quadratic_margin_of_weighted_certificate
    (g : WeilCompactSmoothGV1) (r a m : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g)
    (ρ C : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0 ≤ ρ t)
    (hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t)
    (hCint : Integrable (fun t : ℝ => C t * ρ t))
    (hCzero : (∫ t : ℝ, C t * ρ t) = 0)
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m) + C t) :
    m * energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have h := actual_margin_of_weighted_certificate g r a m hw hr ρ C hρ hmass
    hCint hCzero hcert
  rw [AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm,
    Complex.neg_re] at h
  linarith

end AEGIS.RHKreinCertificateTransferV1

#print axioms AEGIS.RHKreinCertificateTransferV1.symbol_mass_integrable
#print axioms AEGIS.RHKreinCertificateTransferV1.actual_margin_of_weighted_certificate

#print axioms AEGIS.RHKreinCertificateTransferV1.zero_quadratic_margin_of_weighted_certificate
