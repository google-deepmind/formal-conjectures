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

import RHKreinRotTMV1

/-!
# Fast phase rows

For an enclosed phase `Z ≈ exp (i c h)`, the Taylor row of `cos ((c + s) h)` in `s` is
`Re (Z iᵐ) hᵐ / m!`, generated with a running term `hᵐ/m!`; its error is
`e + (1 + e) T_n(r h)` by the complex triangle inequality.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinHatFastV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinRotTMV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open Complex

/-- `Re ((C + S i) iᵐ)`. -/
def sigma (m : ℕ) (C S : ℚ) : ℚ :=
  if m % 2 = 0 then (-1) ^ (m / 2) * C else -((-1) ^ (m / 2) * S)

/-- Row `sigma (k+i) · t_{k+i}` for `i < n`, with running term `t_k = hᵏ / k!`. -/
def phaseRow (C S h : ℚ) : ℕ → ℕ → ℚ → Poly
  | _, 0, _ => []
  | k, n + 1, t => (sigma k C S * t) :: phaseRow C S h (k + 1) n (t * h / ((k : ℚ) + 1))

theorem re_mul_I_pow (C S : ℚ) (m : ℕ) :
    ((((C : ℂ) + (S : ℂ) * I) * I ^ m).re) = (sigma m C S : ℝ) := by
  rw [I_pow_eq]
  unfold sigma
  split_ifs with h
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im]
    push_cast; ring
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im]
    push_cast; ring

theorem eval_phaseRow (C S h : ℚ) (s : ℝ) :
    ∀ (n k : ℕ), eval (phaseRow C S h k n ((h ^ k / k.factorial : ℚ))) s * s ^ k =
      ∑ m ∈ Finset.range n, (sigma (k + m) C S : ℝ) * ((h : ℝ) ^ (k + m) / (k + m).factorial) *
        s ^ (k + m)
  | 0, k => by simp [phaseRow]
  | n + 1, k => by
    rw [Finset.sum_range_succ']
    have hrun : (h ^ k / (k.factorial : ℚ)) * h / ((k : ℚ) + 1) =
        h ^ (k + 1) / ((k + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    have ih := eval_phaseRow C S h s n (k + 1)
    simp only [phaseRow, eval_cons, hrun]
    rw [show ∑ m ∈ Finset.range n, (sigma (k + (m + 1)) C S : ℝ) *
        ((h : ℝ) ^ (k + (m + 1)) / ((k + (m + 1)).factorial : ℝ)) * s ^ (k + (m + 1)) =
      ∑ m ∈ Finset.range n, (sigma (k + 1 + m) C S : ℝ) *
        ((h : ℝ) ^ (k + 1 + m) / ((k + 1 + m).factorial : ℝ)) * s ^ (k + 1 + m) by
      apply Finset.sum_congr rfl; intro m _; rw [show k + (m + 1) = k + 1 + m by omega]]
    rw [← ih]
    push_cast
    simp only [add_zero]
    ring

theorem eval_phaseRow_zero (C S h : ℚ) (n : ℕ) (s : ℝ) :
    eval (phaseRow C S h 0 n 1) s =
      ((((C : ℂ) + (S : ℂ) * I) * expIPartial n (s * h)).re) := by
  have := eval_phaseRow C S h s n 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, zero_add] at this
  rw [this]
  unfold expIPartial
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [show (((C : ℂ) + (S : ℂ) * I) * ((((s * h : ℝ) : ℂ) * I) ^ m / (m.factorial : ℂ))) =
      ((((s * h) ^ m / m.factorial : ℝ)) : ℂ) * (((C : ℂ) + (S : ℂ) * I) * I ^ m) by
    push_cast; ring]
  rw [Complex.re_ofReal_mul, re_mul_I_pow]
  push_cast; ring

/-- Error of one column. -/
def colErr (n : ℕ) (r h : ℚ) (A : CS) : ℚ := A.e + (1 + A.e) * taylorErr n (r * |h|)

theorem col_encl (n : ℕ) (r c h : ℚ) (hr : 0 ≤ r) (hn : 0 < n) (hrh : r * |h| ≤ 1) (A : CS)
    (hA : ZEncl ((c * h : ℚ) : ℝ) A) (s : ℝ) (hs : |s| ≤ r) :
    |Real.cos (((c : ℝ) + s) * h) - eval (phaseRow A.c A.s h 0 n 1) s| ≤ colErr n r h A := by
  rw [eval_phaseRow_zero]
  have hx : |s * (h : ℝ)| ≤ 1 := by
    rw [abs_mul]
    calc |s| * |(h : ℝ)| ≤ r * |(h : ℝ)| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ = ((r * |h| : ℚ) : ℝ) := by push_cast; ring
      _ ≤ 1 := by exact_mod_cast hrh
  have hE := expIPartial_error n (s * h) hn hx
  have hT : |s * (h : ℝ)| ^ n * (((n.succ : ℕ) : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤
      ((taylorErr n (r * |h|) : ℚ) : ℝ) := by
    have := taylor_err_mono n r h s hr hs
    rwa [mul_comm (h : ℝ) s] at this
  have hnZ := norm_zOf_le hA
  have hb1 : ‖Complex.exp (((s * h : ℝ) : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he : (0 : ℝ) ≤ A.e := (norm_nonneg _).trans hA
  have hcos : Real.cos (((c : ℝ) + s) * h) =
      (Complex.exp ((((c * h : ℚ) : ℝ) : ℂ) * I) * Complex.exp (((s * h : ℝ) : ℂ) * I)).re := by
    rw [← Complex.exp_add, show (((c * h : ℚ) : ℝ) : ℂ) * I + ((s * h : ℝ) : ℂ) * I =
      ((((c : ℝ) + s) * h : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
  rw [hcos, show ((A.c : ℂ) + (A.s : ℂ) * I) = zOf A from rfl, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  set a := Complex.exp ((((c * h : ℚ) : ℝ) : ℂ) * I)
  set b := Complex.exp (((s * h : ℝ) : ℂ) * I)
  have e : a * b - zOf A * expIPartial n (s * h) =
      (a - zOf A) * b + zOf A * (b - expIPartial n (s * h)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hb1, mul_one]
  unfold colErr
  push_cast
  apply add_le_add hA
  exact mul_le_mul hnZ (hE.trans hT) (norm_nonneg _) (by linarith)

end AEGIS.RHKreinHatFastV1
