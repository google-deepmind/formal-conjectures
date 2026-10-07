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
import RHKreinL105TailV1
import RHKreinHatAtV1

/-!
# The `L = 21/20` certificate through the Krein–zeta bridge

`Fcert` is rewritten as the integrand of `RHKreinZetaBridgeV1.certificate_zero_quadratic_nonneg`
with `m = 0`: the hats are `H_i = c_i · hatAt (21/20 + (i+1)/50)` and the derivative terms are
`d' = (d₀/2, -d₁/2, -d₂/2, d₃/2, d₄/2)` at the exponents `0, …, 4`.  Given `Fcert ≥ 0` on
`[0, 3000]` (the kernel-checked wide cells) and the tail check, the zero quadratic of every
moment-zero packet with `2r < 21/20` is nonnegative.  A fixed support width; not RH.
AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinL105BridgeV1

open AEGIS.RHKreinZetaBridgeV1
open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinL105TMV1
open AEGIS.RHKreinL105DataV1
open AEGIS.RHKreinL105CheckerV1
open AEGIS.RHKreinL105TailV1
open AEGIS.RHKreinHatAtV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1

def uAt (i : Fin 399) : ℝ := 21 / 20 + ((i : ℕ) + 1) / 50
def cAt (i : Fin 399) : ℚ := cqList.getD i 0
def Hcol (i : Fin 399) (x : ℝ) : ℂ := ((cAt i : ℝ) : ℂ) * hatAt (uAt i) x

def dB (l : Fin 5) : ℂ :=
  match l with
  | ⟨0, _⟩ => ((dq 0 / 2 : ℚ) : ℂ)
  | ⟨1, _⟩ => ((-(dq 1) / 2 : ℚ) : ℂ)
  | ⟨2, _⟩ => ((-(dq 2) / 2 : ℚ) : ℂ)
  | ⟨3, _⟩ => ((dq 3 / 2 : ℚ) : ℂ)
  | ⟨_ + 4, _⟩ => ((dq 4 / 2 : ℚ) : ℂ)
def jB (l : Fin 5) : ℕ := l.val

theorem cqList_length : cqList.length = 399 := by decide +kernel

theorem hatSumL_eq (t : ℝ) : ∀ (l : List ℚ) (h : ℚ),
    hatSumL l h t = ∑ i ∈ Finset.range l.length, ((l.getD i 0 : ℚ) : ℝ) * Real.cos (t * (h + i / 50))
  | [], _ => by simp [hatSumL]
  | a :: l, h => by
    rw [hatSumL, hatSumL_eq t l (h + 1 / 50), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.cast_zero, zero_div, add_zero]
    push_cast
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    congr 2; push_cast; ring

theorem Hcol_fourier_re (i : Fin 399) (t : ℝ) :
    (𝓕 (Hcol i) (t / (2 * Real.pi))).re =
      (cAt i : ℝ) * ((2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * uAt i)) := by
  have h := fourier_const_mul' (hatAt (uAt i)) ((cAt i : ℝ) : ℂ) (t / (2 * Real.pi))
  unfold Hcol
  rw [h, Complex.re_ofReal_mul, hatAt_fourier_re]

theorem hat_sum_re (t : ℝ) :
    (∑ i, 𝓕 (Hcol i) (t / (2 * Real.pi))).re = hatFun t := by
  rw [Complex.re_sum]
  simp only [Hcol_fourier_re]
  unfold hatFun
  rw [hatSumL_eq, cqList_length, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  unfold cAt uAt
  push_cast
  ring_nf

theorem delta_sum_re (t : ℝ) :
    (∑ l, 2 * (dB l * ((I * (t : ℂ)) ^ jB l * Complex.exp (↑(t * (21 / 20 : ℝ)) * I))).re) =
      deltaFun t := by
  rw [Fin.sum_univ_five]
  rw [show jB 0 = 0 from rfl, show jB 1 = 1 from rfl, show jB 2 = 2 from rfl,
    show jB 3 = 3 from rfl, show jB 4 = 4 from rfl,
    show dB 0 = ((dq 0 / 2 : ℚ) : ℂ) from rfl, show dB 1 = ((-(dq 1) / 2 : ℚ) : ℂ) from rfl,
    show dB 2 = ((-(dq 2) / 2 : ℚ) : ℂ) from rfl, show dB 3 = ((dq 3 / 2 : ℚ) : ℂ) from rfl,
    show dB 4 = ((dq 4 / 2 : ℚ) : ℂ) from rfl]
  have e1 : (I * (t : ℂ)) ^ 2 = -((t ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : (I * (t : ℂ)) ^ 3 = -(((t ^ 3 : ℝ) : ℂ) * I) := by
    push_cast; ring_nf; rw [Complex.I_pow_three]; ring
  have e3 : (I * (t : ℂ)) ^ 4 = ((t ^ 4 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_pow_four]; ring
  have e1' : (I * (t : ℂ)) ^ 1 = (t : ℂ) * I := by ring
  rw [pow_zero, e1', e1, e2, e3, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ratCast_re, Complex.ratCast_im, Complex.one_re, Complex.one_im]
  unfold deltaFun L105
  push_cast
  ring

theorem Scert_eq (t : ℝ) : Scert t = symbol t := by
  have hs : Real.exp (-(Real.log 2) / 2) * Real.sqrt 2 = 1 := by
    have h1 : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (Real.exp_pos _).le, ← Real.exp_add]
      rw [show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring, Real.exp_log (by norm_num)]
    rw [h1, ← Real.exp_add, show -Real.log 2 / 2 + Real.log 2 / 2 = 0 by ring, Real.exp_zero]
  have h2 : Real.log 2 * (2 * Real.exp (-(Real.log 2) / 2)) = Real.sqrt 2 * Real.log 2 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have : 2 * Real.exp (-(Real.log 2) / 2) = Real.sqrt 2 := by
      calc 2 * Real.exp (-(Real.log 2) / 2) =
          (Real.sqrt 2 * Real.sqrt 2) * Real.exp (-(Real.log 2) / 2) := by rw [hsq]
        _ = Real.sqrt 2 * (Real.exp (-(Real.log 2) / 2) * Real.sqrt 2) := by ring
        _ = Real.sqrt 2 := by rw [hs, mul_one]
    rw [this]; ring
  have hz : zt t = (1 / 4 : ℂ) + (t : ℂ) * I / 2 := by
    unfold zt; push_cast; ring
  unfold Scert Psi symbol archSymbol
  rw [hz, h2]

theorem hcert105 (hfin : ∀ t : ℝ, 0 ≤ t → t ≤ 3000 → 0 ≤ Fcert t) (P N : ℕ)
    (htail : tailCheck P N 3000 = true) (t : ℝ) :
    0 ≤ Wt t * (Scert t - 0) + (∑ i, 𝓕 (Hcol i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (dB l * ((I * (t : ℂ)) ^ jB l * Complex.exp (↑(t * (21 / 20 : ℝ)) * I))).re := by
  have hF : ∀ s : ℝ, 0 ≤ s → 0 ≤ Fcert s := by
    intro s hs
    by_cases h3 : s ≤ 3000
    · exact hfin s hs h3
    · exact tail_nonneg P N 3000 htail s (by push_cast; linarith)
  have hall : 0 ≤ Fcert t := by
    rcases le_total 0 t with ht | ht
    · exact hF t ht
    · rw [← Fcert_even]; exact hF (-t) (by linarith)
  rw [hat_sum_re, delta_sum_re, Scert_eq, sub_zero]
  unfold Fcert at hall
  unfold Wt
  linarith

theorem L105_le_log3 : (21 / 20 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (21 / 20) = Real.exp 1 * Real.exp (1 / 20) := by
    rw [← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound' (x := 1 / 20) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  rw [h1]
  have hp : 0 < Real.exp (1 / 20) := Real.exp_pos _
  nlinarith

/-- **The `L = 21/20` window.**  From the kernel-checked wide cells on `[0, 3000]` and the tail
check, the zeta zero quadratic is nonnegative on every moment-zero packet of logarithmic
half-width `r` with `2r < 21/20`. -/
theorem zero_quadratic_nonneg_L105
    (hfin : ∀ t : ℝ, 0 ≤ t → t ≤ 3000 → 0 ≤ Fcert t) (P N : ℕ)
    (htail : tailCheck P N 3000 = true)
    (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g) (r a : ℝ) (hr : 0 ≤ r)
    (hrL : 2 * r < 21 / 20) (hw : HalfWidthAt g r a) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  refine certificate_zero_quadratic_nonneg (21 / 20) 0 le_rfl L105_le_log3 Hcol
    (fun i => continuous_const.mul (hatAt_continuous (uAt i)))
    (fun i => (hatAt_integrable (uAt i)).const_mul _)
    (fun i => ?_) (fun i u hu => ?_) dB jB (hcert105 hfin P N htail) g hmom r a hr hrL hw
  · refine ((hatAt_fourier_integrable (uAt i)).const_mul ((cAt i : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    exact (fourier_const_mul' (hatAt (uAt i)) _ ξ).symm
  · unfold Hcol
    rw [hatAt_zero (uAt i) (by unfold uAt; have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _; linarith),
      mul_zero]

end AEGIS.RHKreinL105BridgeV1

#print axioms AEGIS.RHKreinL105BridgeV1.zero_quadratic_nonneg_L105
