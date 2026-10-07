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

import AEGISOverlay.RHKreinDigammaMonotonicityV1
import RHKreinPrimeSymbolV1
import RHKreinExplicitCorrectionV1

/-!
# Exact infinite-tail bounds for the rational order-19 certificate

The digamma endpoint is evaluated in exact rational arithmetic. The existing
series and monotonicity theorems transport it to every real frequency outside
[-300, 300]. All logarithmic and prime factors refer to the actual symbol in
`RHKreinPrimeSymbolV1`. No ball-arithmetic output is a theorem premise.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinRationalCertificateV1

open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinExplicitCorrectionV1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Exact rational endpoint calculation, with sixty-four proved series terms. -/
theorem digamma_tail_endpoint :
    (4 : ℝ) ≤ -(5792 / 10000 : ℝ) +
      (∑ n ∈ Finset.range 64, quarterTerm 300 n) -
      (3 / 4 : ℝ) * (1 / ((64 : ℝ) + 1 / 4) +
        1 / ((64 : ℝ) + 1 / 4) ^ 2) := by
  norm_num [quarterTerm, Finset.sum_range_succ]

/-- The actual quarter-line digamma real part is at least four on the tail. -/
theorem digamma_tail_lower (t : ℝ) (ht : 300 ≤ |t|) :
    (4 : ℝ) ≤ (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re := by
  have hs : (300 : ℝ) ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  exact digamma_tail_endpoint.trans
    (digamma_quarter_certificate_lower_of_sq_le 300 t 64 hs)

private theorem log_two_le_seven_tenths : Real.log 2 ≤ (7 / 10 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h
  linarith

private theorem log_pi_le_seven_fifths : Real.log Real.pi ≤ (7 / 5 : ℝ) := by
  have h : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [log_two_le_seven_tenths]

private theorem prime_amplitude_le_twenty_one_twentieths :
    Real.sqrt 2 * Real.log 2 ≤ (21 / 20 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul hs log_two_le_seven_tenths hl (by norm_num : (0 : ℝ) ≤ 3 / 2)
  norm_num at hm
  exact hm

/-- A uniform positive lower bound for the actual finite-window Weil symbol. -/
theorem actual_symbol_tail_lower (t : ℝ) (ht : 300 ≤ |t|) :
    (3 / 2 : ℝ) ≤ symbol t := by
  have hp : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (t * Real.log 2)) hp
  simp only [mul_one] at hc
  unfold symbol archSymbol
  linarith [digamma_tail_lower t ht, log_pi_le_seven_fifths,
    prime_amplitude_le_twenty_one_twentieths]

/-- A polynomial envelope for the exact certificate fits below its rational
spectral budget on the entire infinite tail. -/
theorem correction_polynomial_tail_bound (x : ℝ) (hx : 300 ≤ x) :
    772000 + 4900 * x + 292 * x ^ 2 + 13 * x ^ 3 + x ^ 4 ≤
      (17 / 16 : ℝ) * (x ^ 2 + 1 / 4) ^ 2 := by
  have hy : 0 ≤ x - 300 := by linarith
  have hp : 0 ≤ (x - 300) ^ 4 / 16 + 62 * (x - 300) ^ 3 +
      (696273 / 32 : ℝ) * (x - 300) ^ 2 +
      (12240875 / 4 : ℝ) * (x - 300) + 32454608017 / 256 := by positivity
  nlinarith only [hp]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Exact coefficient arithmetic, independent of interval-enclosure output. -/
theorem hat_coefficient_budget :
    (∑ j : Fin 199, |(hatCoefficient j : ℝ)|) ≤ 18125000 := by
  have h : (∑ j : Fin 199, |hatCoefficient j|) ≤ (18125000 : ℚ) := by
    norm_num [hatCoefficient, Fin.sum_univ_succ]
  exact_mod_cast h

private theorem spline_coefficient_budget (j : Fin 5) :
    |(splineCoefficient j : ℝ)| ≤ ![(47000 : ℝ), 4900, 292, 13, 1] j := by
  fin_cases j <;> norm_num [splineCoefficient]

private theorem abs_phase_le_one (j : Fin 5) (t : ℝ) :
    |if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
      else Real.sin (t * (1619 / 2000))| ≤ 1 := by
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

/-- A global polynomial bound for the Fourier expression of the actual
rational genuine-function correction. -/
theorem abs_correctionSymbol_le_polynomial (t : ℝ) :
    |correctionSymbol t| ≤
      772000 + 4900 * |t| + 292 * |t| ^ 2 + 13 * |t| ^ 3 + |t| ^ 4 := by
  have hh : |∑ j : Fin 199, (hatCoefficient j : ℝ) *
      Real.cos (t * hatCenter j)| ≤ 18125000 := by
    calc
      |∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)| ≤
          ∑ j : Fin 199, |(hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 199, |(hatCoefficient j : ℝ)| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 18125000 := hat_coefficient_budget
  have hhat : |(2 / 50 : ℝ) * Real.sinc (t / 100) ^ 2 *
      (∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j))| ≤
      725000 := by
    have hp : |Real.sinc (t / 100)| ^ 2 ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
    rw [abs_mul, abs_mul, abs_pow]
    norm_num
    have hb := mul_le_mul hp hh (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    rw [sq_abs] at hb
    nlinarith only [hb]
  have hs : |∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
        else Real.sin (t * (1619 / 2000)))| ≤
      47000 + 4900 * |t| + 292 * |t| ^ 2 + 13 * |t| ^ 3 + |t| ^ 4 := by
    calc
      |∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
          (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
            else Real.sin (t * (1619 / 2000)))| ≤
          ∑ j : Fin 5, |(splineCoefficient j : ℝ) * t ^ j.val *
            (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
              else Real.sin (t * (1619 / 2000)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 5, (![(47000 : ℝ), 4900, 292, 13, 1] j) * |t| ^ j.val := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_pow]
        calc
          |(splineCoefficient j : ℝ)| * |t| ^ j.val *
              |if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
                else Real.sin (t * (1619 / 2000))| ≤
              |(splineCoefficient j : ℝ)| * |t| ^ j.val :=
            mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
              (abs_phase_le_one j t)
          _ ≤ _ := mul_le_mul_of_nonneg_right (spline_coefficient_budget j)
            (pow_nonneg (abs_nonneg _) _)
      _ = _ := by simp [Fin.sum_univ_succ]; ring
  have he : |Real.sinc (t / 2000) ^ 19 *
      (∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
        (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
          else Real.sin (t * (1619 / 2000))))| ≤
      47000 + 4900 * |t| + 292 * |t| ^ 2 + 13 * |t| ^ 3 + |t| ^ 4 := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ 1 * |∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
          (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
            else Real.sin (t * (1619 / 2000)))| :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hs
  unfold correctionSymbol
  exact (abs_add_le _ _).trans (by linarith only [hhat, he])

/-- The explicit correction has a uniform rational normalized tail budget. -/
theorem actual_correction_tail_bound (t : ℝ) (ht : 300 ≤ |t|) :
    |correctionSymbol t| ≤ (17 / 16 : ℝ) * (t ^ 2 + 1 / 4) ^ 2 := by
  simpa only [sq_abs] using (abs_correctionSymbol_le_polynomial t).trans
    (correction_polynomial_tail_bound |t| ht)

/-- Unconditional pointwise certificate for the entire infinite tail,
with a positive reserve in the exact convention consumed by the Weil bridge. -/
theorem corrected_symbol_tail (t : ℝ) (ht : 300 ≤ |t|) :
    (3 / 8 : ℝ) * (t ^ 2 + 1 / 4) ^ 2 ≤
      (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) + correctionSymbol t := by
  have hs := actual_symbol_tail_lower t ht
  have hc := actual_correction_tail_bound t ht
  have hl := neg_abs_le (correctionSymbol t)
  have hw : 0 ≤ (t ^ 2 + 1 / 4) ^ 2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hs hw
  nlinarith only [hc, hl, hm]

/-- The required nonnegative sign follows without a numerical tail premise. -/
theorem corrected_symbol_tail_nonnegative (t : ℝ) (ht : 300 ≤ |t|) :
    0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) + correctionSymbol t := by
  exact (by positivity : (0 : ℝ) ≤ (3 / 8 : ℝ) * (t ^ 2 + 1 / 4) ^ 2).trans
    (corrected_symbol_tail t ht)

end AEGIS.RHKreinRationalCertificateV1

#print axioms AEGIS.RHKreinRationalCertificateV1.digamma_tail_endpoint
#print axioms AEGIS.RHKreinRationalCertificateV1.digamma_tail_lower
#print axioms AEGIS.RHKreinRationalCertificateV1.actual_symbol_tail_lower
#print axioms AEGIS.RHKreinRationalCertificateV1.correction_polynomial_tail_bound

#print axioms AEGIS.RHKreinRationalCertificateV1.hat_coefficient_budget
#print axioms AEGIS.RHKreinRationalCertificateV1.abs_correctionSymbol_le_polynomial
#print axioms AEGIS.RHKreinRationalCertificateV1.actual_correction_tail_bound
#print axioms AEGIS.RHKreinRationalCertificateV1.corrected_symbol_tail
#print axioms AEGIS.RHKreinRationalCertificateV1.corrected_symbol_tail_nonnegative
