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

import AEGISOverlay.RHKreinDigammaLowerBoundV1

/-!
# Quarter-line digamma monotonicity for exact certificate endpoints

The established complex digamma series is mapped through the real part.
Each explicit term increases with the square of the angular frequency.
Absolute summability permits termwise comparison. This justifies using a
finite-interval left endpoint and a single infinite-tail starting point in
`research/rh/krein_order19_v1/certify.py`.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinDigammaMonotonicityV1

open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesRealV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1

/-- Every rational summand increases with squared angular frequency. -/
theorem quarterTerm_mono_of_sq_le (s t : ℝ) (hst : s ^ 2 ≤ t ^ 2) (n : ℕ) :
    quarterTerm s n ≤ quarterTerm t n := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  have hd : 0 < ((n : ℝ) + 1 / 4) ^ 2 + s ^ 2 / 4 := by positivity
  have hden : ((n : ℝ) + 1 / 4) ^ 2 + s ^ 2 / 4 ≤
      ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by linarith
  have hdiv := div_le_div_of_nonneg_left hx.le hd hden
  unfold quarterTerm
  linarith

/-- The established complex series supplies this exact real `HasSum`. -/
theorem quarterTerm_hasSum (t : ℝ) :
    HasSum (quarterTerm t)
      ((Complex.digamma (quarterPoint t)).re + Real.eulerMascheroniConstant) := by
  have hz : 0 < (quarterPoint t).re := by norm_num [quarterPoint]
  have hs : Summable (seriesTerm (quarterPoint t)) :=
    (summable_norm_seriesTerm_v1 (quarterPoint t) hz).of_norm
  have hc := hs.hasSum
  rw [← digamma_series_halfPlane_v1 (quarterPoint t) hz] at hc
  simpa only [← quarterTerm_eq_seriesTerm_re, Complex.add_re, Complex.ofReal_re]
    using Complex.hasSum_re hc

/-- Actual Mathlib digamma comparison, valid for arbitrary real frequencies. -/
theorem digamma_quarter_mono_of_sq_le (s t : ℝ) (hst : s ^ 2 ≤ t ^ 2) :
    (Complex.digamma ((1 / 4 : ℂ) + (s : ℂ) * I / 2)).re ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re := by
  have hs := quarterTerm_hasSum s
  have ht := quarterTerm_hasSum t
  have h := le_of_tendsto_of_tendsto' hs.tendsto_sum_nat ht.tendsto_sum_nat
    (fun N : ℕ => Finset.sum_le_sum
      (fun n (_hn : n ∈ Finset.range N) => quarterTerm_mono_of_sq_le s t hst n))
  dsimp [quarterPoint] at h
  linarith

/-- The actual digamma real part is nondecreasing on nonnegative frequencies. -/
theorem digamma_quarter_monotoneOn_nonnegative :
    MonotoneOn (fun t : ℝ =>
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re) (Set.Ici 0) := by
  intro s hs t ht hst
  apply digamma_quarter_mono_of_sq_le s t
  have hpos : 0 ≤ t + s := add_nonneg ht hs
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) hpos]

/-- The rational lower bound at one frequency holds at every larger squared
frequency. This is the finite-grid endpoint and infinite-tail interface. -/
theorem digamma_quarter_certificate_lower_of_sq_le
    (s t : ℝ) (N : ℕ) (hst : s ^ 2 ≤ t ^ 2) :
    -(5792 / 10000 : ℝ) + (∑ n ∈ Finset.range N, quarterTerm s n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) +
          1 / ((N : ℝ) + 1 / 4) ^ 2) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re :=
  (digamma_quarter_certificate_lower s N).trans (digamma_quarter_mono_of_sq_le s t hst)

end AEGIS.RHKreinDigammaMonotonicityV1

#print axioms AEGIS.RHKreinDigammaMonotonicityV1.quarterTerm_mono_of_sq_le
#print axioms AEGIS.RHKreinDigammaMonotonicityV1.quarterTerm_hasSum
#print axioms AEGIS.RHKreinDigammaMonotonicityV1.digamma_quarter_mono_of_sq_le
#print axioms AEGIS.RHKreinDigammaMonotonicityV1.digamma_quarter_monotoneOn_nonnegative
#print axioms AEGIS.RHKreinDigammaMonotonicityV1.digamma_quarter_certificate_lower_of_sq_le
