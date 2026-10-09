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

import AEGISOverlay.RHKreinCorrectionM8BoundV1
import AEGISOverlay.RHKreinCorrectionTaylorBridgeV1

/-!
# Canonical M8 and Taylor-jet error transport

The unchanged PR52 producer is rebound to the original monolithic symbol
via a declaration-free import adapter. The one-line compact-support repair
is explicit in the replay manifest. No coefficient or symbol is replaced.

The new cell lemmas include the cell center and expose, rather than assume
away, the remaining analytic Taylor-jet and polynomial-enclosure obligations.
No serialized cell, pointwise certificate or RH statement is concluded.
AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinM8AnalyticV1

open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinM8CertificateV1
open AEGIS.RHKreinCorrectionM8BoundV1
open AEGIS.RHKreinFiniteIntervalKernelV1

/-- The reused proof now refers directly to the original monolithic definition. -/
theorem correctionSymbol_eighth_abs_le_serialized (t : ℝ) :
    |iteratedDeriv 8 correctionSymbol t| ≤ (serializedM8Q : ℝ) :=
  correctionSymbol_eighth_derivative_le_serialized t

private theorem budget_nonneg : (0 : ℝ) ≤ (serializedM8Q : ℝ) := by
  exact_mod_cast serializedM8Q_pos_v1.le

/-- Degree-seven remainder for every center and argument, including their equality. -/
theorem correction_taylor7_remainder (c x : ℝ) :
    |correctionSymbol x - centeredTaylorEval correctionSymbol 7 c x| ≤
      (serializedM8Q : ℝ) * |x - c| ^ 8 / 40320 := by
  by_cases hcx : c = x
  · subst x
    rw [centeredTaylorEval_self correctionSymbol 7 c
      (correctionSymbol_contDiff_eight.contDiffAt.of_le (by norm_num))]
    simp
  · exact centeredTaylor7_remainder_of_ne correctionSymbol c x
      (serializedM8Q : ℝ) hcx correctionSymbol_contDiff_eight
      correctionSymbol_eighth_abs_le_serialized

/-- A closed cell has a uniform remainder budget, without excluding its center. -/
theorem correction_taylor7_cell_remainder (c x r : ℝ)
    (_hr : 0 ≤ r) (hx : |x - c| ≤ r) :
    |correctionSymbol x - centeredTaylorEval correctionSymbol 7 c x| ≤
      (serializedM8Q : ℝ) * r ^ 8 / 40320 := by
  refine (correction_taylor7_remainder c x).trans ?_
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg (x - c)) hx 8) budget_nonneg
  · norm_num

/-- Normalized ordinary derivative used by the degree-seven Taylor jet. -/
def exactJetCoefficient (c : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ)⁻¹ * iteratedDeriv k correctionSymbol c

/-- A finite approximating polynomial; rational coefficients may be coerced here. -/
def jetPolynomial7 (q : ℕ → ℝ) (c x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 8, q k * (x - c) ^ k

theorem centeredTaylor_eq_exactJet (c x : ℝ) :
    centeredTaylorEval correctionSymbol 7 c x =
      jetPolynomial7 (exactJetCoefficient c) c x := by
  unfold centeredTaylorEval jetPolynomial7 exactJetCoefficient
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Coefficient enclosures give a uniform polynomial error over the cell. -/
theorem jetPolynomial7_error (c x r : ℝ) (q e : ℕ → ℝ)
    (hx : |x - c| ≤ r)
    (hjet : ∀ k ∈ Finset.range 8, |exactJetCoefficient c k - q k| ≤ e k) :
    |jetPolynomial7 (exactJetCoefficient c) c x - jetPolynomial7 q c x| ≤
      ∑ k ∈ Finset.range 8, e k * r ^ k := by
  unfold jetPolynomial7
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  rw [← sub_mul, abs_mul, abs_pow]
  have he0 : 0 ≤ e k := (abs_nonneg _).trans (hjet k hk)
  exact mul_le_mul (hjet k hk)
    (pow_le_pow_left₀ (abs_nonneg (x - c)) hx k) (by positivity) he0

/-- Combined analytic remainder and jet-rounding error for the actual correction. -/
theorem correction_jet7_error (c x r : ℝ) (q e : ℕ → ℝ)
    (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hjet : ∀ k ∈ Finset.range 8, |exactJetCoefficient c k - q k| ≤ e k) :
    |correctionSymbol x - jetPolynomial7 q c x| ≤
      (serializedM8Q : ℝ) * r ^ 8 / 40320 +
        ∑ k ∈ Finset.range 8, e k * r ^ k := by
  calc
    |correctionSymbol x - jetPolynomial7 q c x| ≤
        |correctionSymbol x - centeredTaylorEval correctionSymbol 7 c x| +
          |centeredTaylorEval correctionSymbol 7 c x - jetPolynomial7 q c x| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (correctionSymbol x - centeredTaylorEval correctionSymbol 7 c x)
          (centeredTaylorEval correctionSymbol 7 c x - jetPolynomial7 q c x)
    _ ≤ _ := add_le_add (correction_taylor7_cell_remainder c x r hr hx) (by
      rw [centeredTaylor_eq_exactJet]
      exact jetPolynomial7_error c x r q e hx hjet)

/-- The lower cell bound explicitly retains analytic jet-enclosure premises. -/
theorem correction_lower_of_jet_enclosures (c x r lo : ℝ) (q e : ℕ → ℝ)
    (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hjet : ∀ k ∈ Finset.range 8, |exactJetCoefficient c k - q k| ≤ e k)
    (hpoly : lo ≤ jetPolynomial7 q c x) :
    lo - ((serializedM8Q : ℝ) * r ^ 8 / 40320 +
      ∑ k ∈ Finset.range 8, e k * r ^ k) ≤ correctionSymbol x := by
  have h := (abs_le.mp (correction_jet7_error c x r q e hr hx hjet)).1
  linarith

/-- Specialization with no jet-rounding error; still requires the actual polynomial bound. -/
theorem correction_lower_of_exact_taylor (c x r lo : ℝ)
    (hr : 0 ≤ r) (hx : |x - c| ≤ r)
    (hpoly : lo ≤ centeredTaylorEval correctionSymbol 7 c x) :
    lo - (serializedM8Q : ℝ) * r ^ 8 / 40320 ≤ correctionSymbol x := by
  have h := (abs_le.mp (correction_taylor7_cell_remainder c x r hr hx)).1
  linarith

end AEGIS.RHKreinM8AnalyticV1

#print axioms AEGIS.RHKreinM8AnalyticV1.correctionSymbol_eighth_abs_le_serialized
#print axioms AEGIS.RHKreinM8AnalyticV1.correction_taylor7_remainder
#print axioms AEGIS.RHKreinM8AnalyticV1.correction_taylor7_cell_remainder
#print axioms AEGIS.RHKreinM8AnalyticV1.centeredTaylor_eq_exactJet
#print axioms AEGIS.RHKreinM8AnalyticV1.jetPolynomial7_error
#print axioms AEGIS.RHKreinM8AnalyticV1.correction_jet7_error
#print axioms AEGIS.RHKreinM8AnalyticV1.correction_lower_of_jet_enclosures
#print axioms AEGIS.RHKreinM8AnalyticV1.correction_lower_of_exact_taylor
