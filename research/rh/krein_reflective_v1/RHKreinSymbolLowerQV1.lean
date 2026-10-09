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
import AEGISOverlay.RHKreinDigammaMonotonicityV1
import RHEulerGammaSharpV1
import RHKreinPrimeSymbolV1

/-!
# Rational symbol floor from a left endpoint

For `0 ≤ lo ≤ t`,

  `archLQ lo - A₀ cos (t L₀) - A₀ t / 10¹⁰ - 2/10⁹ ≤ symbol t`,

where `archLQ lo` is the 128-term quarter-line digamma partial sum at `lo` with the explicit
tail, `γ < 0.5773`, and a rational `log π` upper bound; `A₀`, `L₀` are rational surrogates for
`√2 log 2` and `log 2`.  The prime cosine is kept, not replaced by `1`.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSymbolLowerQV1

open Complex
open AEGIS.RHKreinDigammaLowerBoundV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHEulerGammaSharpV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1

def quarterTermQ (t : ℚ) (n : ℕ) : ℚ :=
  1 / ((n : ℚ) + 1) - ((n : ℚ) + 1 / 4) / (((n : ℚ) + 1 / 4) ^ 2 + t ^ 2 / 4)

def qsum (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => qsum t n + quarterTermQ t n

theorem qsum_cast (t : ℚ) : ∀ N : ℕ, ((qsum t N : ℚ) : ℝ) = ∑ n ∈ Finset.range N, quarterTerm t n
  | 0 => by simp [qsum]
  | N + 1 => by
    rw [Finset.sum_range_succ, ← qsum_cast t N]
    simp only [qsum, quarterTermQ, quarterTerm]
    push_cast; ring

def archLQ (lo : ℚ) : ℚ :=
  -5773 / 10000 + qsum lo 128 - 3 / 4 * (1 / (128 + 1 / 4) + 1 / (128 + 1 / 4) ^ 2) -
    1144729886 / 1000000000

def A0 : ℚ := 1414213562 / 1000000000 * (6931471806 / 10000000000)
def L0 : ℚ := 287209 / 414355

theorem logPi_upper : Real.log Real.pi ≤ (1144729886 / 1000000000 : ℝ) := by
  let x : ℝ := (1144729886 / 2000000000 : ℝ)
  let p : ℝ := ∑ m ∈ Finset.range 16, x ^ m / m.factorial
  let e : ℝ := |x| ^ 16 * ((17 : ℝ) / (Nat.factorial 16 * 16))
  have hb := Real.exp_bound (x := x) (n := 16) (by norm_num [x]) (by norm_num)
  have hlo : p - e ≤ Real.exp x := by
    rw [abs_sub_le_iff] at hb
    dsimp [p, e]
    linarith [hb.1]
  have hp : 0 ≤ p - e := by
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg]
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hsquare : (p - e) ^ 2 ≤ (Real.exp x) ^ 2 := by nlinarith
  have hpi : Real.pi ≤ (p - e) ^ 2 := by
    have h := Real.pi_lt_d20
    norm_num [p, e, x, Finset.sum_range_succ, abs_of_nonneg] at h ⊢
    linarith
  have hq : Real.exp (1144729886 / 1000000000 : ℝ) = (Real.exp x) ^ 2 := by
    rw [show (1144729886 / 1000000000 : ℝ) = x + x by norm_num [x], Real.exp_add]
    ring
  apply (Real.log_le_iff_le_exp Real.pi_pos).2
  rw [hq]
  exact hpi.trans hsquare

theorem amp_close : |Real.sqrt 2 * Real.log 2 - (A0 : ℝ)| ≤ 2 / 10 ^ 9 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hsl : (1414213562 / 1000000000 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 ≤ (1414213563 / 1000000000 : ℝ) := by nlinarith
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  unfold A0
  push_cast
  rw [abs_le]
  constructor <;> norm_num at hl1 hl2 ⊢ <;> nlinarith

theorem log2_close : |Real.log 2 - (L0 : ℝ)| ≤ 1 / 10 ^ 10 := by
  have h := Real.log_two_near_10
  unfold L0; push_cast; exact h

theorem symbol_lower (lo : ℚ) (t : ℝ) (h0 : (0 : ℝ) ≤ lo) (ht : (lo : ℝ) ≤ t) :
    (archLQ lo : ℝ) - A0 * Real.cos (t * L0) - A0 * t / 10 ^ 10 - 2 / 10 ^ 9 ≤ symbol t := by
  have hst : (lo : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
  have hfin := digamma_quarter_finite_lower (lo : ℝ) 128
  have hmono := digamma_quarter_mono_of_sq_le (lo : ℝ) t hst
  have hg := gamma_lt_5773
  have hlp := logPi_upper
  rw [← qsum_cast] at hfin
  unfold quarterPoint at hfin
  set D0 := (Complex.digamma ((1 / 4 : ℂ) + (((lo : ℚ) : ℝ) : ℂ) * I / 2)).re with hD0
  set D1 := (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re with hD1
  have hamp := amp_close
  have hl2 := log2_close
  have hA0 : (0 : ℝ) ≤ A0 := by unfold A0; positivity
  have ht0 : 0 ≤ t := h0.trans ht
  have hcos : |Real.cos (t * Real.log 2) - Real.cos (t * L0)| ≤ t / 10 ^ 10 := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg ht0]
    calc t * |Real.log 2 - (L0 : ℝ)| ≤ t * (1 / 10 ^ 10) :=
          mul_le_mul_of_nonneg_left hl2 ht0
      _ = t / 10 ^ 10 := by ring
  have hc1 : (A0 : ℝ) * Real.cos (t * Real.log 2) ≤ A0 * Real.cos (t * L0) + A0 * (t / 10 ^ 10) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hA0
    linarith [le_abs_self (Real.cos (t * Real.log 2) - Real.cos (t * L0))]
  have hc2 : (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) ≤ 2 / 10 ^ 9 := by
    calc (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) ≤
        |(Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2)| := le_abs_self _
      _ = |Real.sqrt 2 * Real.log 2 - A0| * |Real.cos (t * Real.log 2)| := abs_mul _ _
      _ ≤ (2 / 10 ^ 9) * 1 :=
          mul_le_mul hamp (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ = 2 / 10 ^ 9 := by ring
  unfold symbol archSymbol archLQ
  rw [← hD1]
  push_cast
  have e : Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2) =
      A0 * Real.cos (t * Real.log 2) +
        (Real.sqrt 2 * Real.log 2 - A0) * Real.cos (t * Real.log 2) := by ring
  rw [e]
  norm_num at hfin ⊢
  linarith

end AEGIS.RHKreinSymbolLowerQV1
