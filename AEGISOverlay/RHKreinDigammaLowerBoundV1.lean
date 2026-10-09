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

import WeilDigammaSeriesHalfPlaneV1
import RHEulerGammaV13
import Mathlib.Tactic

/-!
# Exact finite lower bound for the actual quarter-line digamma function

This is the rational-tail inequality used in
`research/rh/krein_order19_v1/certify.py`. It follows from the repository's
proved series for Mathlib's `Complex.digamma`. A telescoping minorant bounds
the entire tail; there is no numerical premise and no finite-grid inference.
-/

open Filter Complex
open scoped Topology BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinDigammaLowerBoundV1

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesRealV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1

/-- The exact rational summand in the real quarter-line digamma series. -/
def quarterTerm (t : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) -
    ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4)

/-- The argument of Mathlib's actual digamma function. -/
def quarterPoint (t : ℝ) : ℂ := (1 / 4 : ℂ) + (t : ℂ) * I / 2

private theorem quarterPoint_re (t : ℝ) : (quarterPoint t).re = 1 / 4 := by
  simp [quarterPoint]

/-- This finite summand is the real part of the already-proved complex series. -/
theorem quarterTerm_eq_seriesTerm_re (t : ℝ) (n : ℕ) :
    quarterTerm t n = (seriesTerm (quarterPoint t) n).re := by
  have hfirst : (1 / ((n : ℂ) + 1)).re = 1 / ((n : ℝ) + 1) := by
    have hcast : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    norm_cast
  have hzre : (quarterPoint t + n).re = (n : ℝ) + 1 / 4 := by
    simp [quarterPoint]
    ring
  have hzim : (quarterPoint t + n).im = t / 2 := by simp [quarterPoint]
  have hsq : normSq (quarterPoint t + n) = ((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hsecond : (1 / (quarterPoint t + n)).re =
      ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) := by
    rw [one_div, Complex.inv_re, hzre, hsq]
  simp only [quarterTerm, seriesTerm, Complex.sub_re, hfirst, hsecond]

private theorem quarterTerm_lower (t : ℝ) (n : ℕ) :
    -(3 / 4 : ℝ) / ((n : ℝ) + 1 / 4) ^ 2 ≤ quarterTerm t n := by
  let x : ℝ := (n : ℝ) + 1 / 4
  have hx : 0 < x := by dsimp [x]; positivity
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hrecip : x / (x ^ 2 + t ^ 2 / 4) ≤ 1 / x := by
    calc
      x / (x ^ 2 + t ^ 2 / 4) ≤ x / x ^ 2 :=
        div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx) (by nlinarith [sq_nonneg t])
      _ = 1 / x := by field_simp
  have hprod : x ^ 2 ≤ ((n : ℝ) + 1) * x := by dsimp [x]; nlinarith
  have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (sq_pos_of_pos hx) hprod
  have heq : 1 / ((n : ℝ) + 1) - 1 / x =
      -(3 / 4 : ℝ) / (((n : ℝ) + 1) * x) := by
    dsimp [x]
    field_simp
    ring
  change -(3 / 4 : ℝ) / x ^ 2 ≤
    1 / ((n : ℝ) + 1) - x / (x ^ 2 + t ^ 2 / 4)
  simp only [neg_div] at heq ⊢
  linarith

private theorem reciprocal_square_telescoper (q x : ℝ)
    (hq : 0 < q) (hqx : q ≤ x) :
    1 / x ^ 2 ≤ (1 + 1 / q) * (1 / x - 1 / (x + 1)) := by
  have hx : 0 < x := lt_of_lt_of_le hq hqx
  have hx1 : 0 < x + 1 := by linarith
  have hxq : x ≤ x ^ 2 / q := by
    apply (le_div_iff₀ hq).2
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hqx)]
  have heq : (1 + 1 / q) * (1 / x - 1 / (x + 1)) =
      (1 + 1 / q) / (x * (x + 1)) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) (mul_pos hx hx1)).2
  simp only [div_eq_mul_inv, one_mul] at hxq ⊢
  nlinarith

/-- A telescoping lower bound for each term of the omitted tail. -/
theorem quarterTerm_telescoping_lower (t : ℝ) (N n : ℕ) (hN : N ≤ n) :
    -(3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) *
      (1 / ((n : ℝ) + 1 / 4) - 1 / ((n : ℝ) + 1 / 4 + 1)) ≤
        quarterTerm t n := by
  have hrecip := reciprocal_square_telescoper
    ((N : ℝ) + 1 / 4) ((n : ℝ) + 1 / 4)
    (by positivity) (by
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hN
      linarith)
  have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hterm := quarterTerm_lower t n
  simp only [div_eq_mul_inv] at hmul hterm ⊢
  nlinarith only [hmul, hterm]

private theorem finite_tail_lower (t : ℝ) (N k : ℕ) :
    (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) / ((N : ℝ) + 1 / 4) +
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) /
          ((N + k : ℕ) + 1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.range (N + k), quarterTerm t n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := quarterTerm_telescoping_lower t N (N + k) (by omega)
    rw [Nat.add_succ, Finset.sum_range_succ]
    push_cast at ht ih ⊢
    rw [show (N : ℝ) + k + 1 + 1 / 4 = (N : ℝ) + k + 1 / 4 + 1 by ring]
    simp only [div_eq_mul_inv] at ht ih ⊢
    nlinarith only [ht, ih]

private theorem quarter_partial_sums_tendsto (t : ℝ) :
    Tendsto (fun k : ℕ => ∑ n ∈ Finset.range k, quarterTerm t n)
      atTop (𝓝 ((Complex.digamma (quarterPoint t)).re + Real.eulerMascheroniConstant)) := by
  have hz : 0 < (quarterPoint t).re := by rw [quarterPoint_re]; norm_num
  have hs : Summable (seriesTerm (quarterPoint t)) :=
    (summable_norm_seriesTerm_v1 (quarterPoint t) hz).of_norm
  have hc := hs.hasSum.tendsto_sum_nat
  rw [← digamma_series_halfPlane_v1 (quarterPoint t) hz] at hc
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  simpa only [Function.comp_def, Complex.re_sum, ← quarterTerm_eq_seriesTerm_re,
    Complex.add_re, Complex.ofReal_re] using hr

/-- Exact finite lower bound with the true Euler constant. -/
theorem digamma_quarter_finite_lower (t : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant + (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) +
          1 / ((N : ℝ) + 1 / 4) ^ 2) ≤
      (Complex.digamma (quarterPoint t)).re := by
  have hshift : Tendsto (fun k : ℕ => N + k) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  have hlim := (quarter_partial_sums_tendsto t).comp hshift
  have hbound : ∀ k : ℕ,
      (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) / ((N : ℝ) + 1 / 4) ≤
        ∑ n ∈ Finset.range (N + k), quarterTerm t n := by
    intro k
    have h := finite_tail_lower t N k
    have hp : 0 ≤ (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) /
        ((N + k : ℕ) + 1 / 4 : ℝ) := by positivity
    linarith
  have h := ge_of_tendsto' hlim hbound
  have heq : (3 / 4 : ℝ) * (1 + 1 / ((N : ℝ) + 1 / 4)) /
      ((N : ℝ) + 1 / 4) =
      (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) + 1 / ((N : ℝ) + 1 / 4) ^ 2) := by
    field_simp
  rw [heq] at h
  linarith

/-- The exact all-real-frequency lower bound consumed by the rational
order-19 certificate, using the kernel-proved upper bound for Euler's constant. -/
theorem digamma_quarter_certificate_lower (t : ℝ) (N : ℕ) :
    -(5792 / 10000 : ℝ) + (∑ n ∈ Finset.range N, quarterTerm t n) -
        (3 / 4 : ℝ) * (1 / ((N : ℝ) + 1 / 4) +
          1 / ((N : ℝ) + 1 / 4) ^ 2) ≤
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re := by
  have h := digamma_quarter_finite_lower t N
  have hg := AEGIS.RHEulerGammaV13.gamma_lt
  dsimp [quarterPoint] at h
  linarith

end AEGIS.RHKreinDigammaLowerBoundV1

#print axioms AEGIS.RHKreinDigammaLowerBoundV1.quarterTerm_eq_seriesTerm_re
#print axioms AEGIS.RHKreinDigammaLowerBoundV1.quarterTerm_telescoping_lower
#print axioms AEGIS.RHKreinDigammaLowerBoundV1.digamma_quarter_finite_lower
#print axioms AEGIS.RHKreinDigammaLowerBoundV1.digamma_quarter_certificate_lower
