import sys
from fractions import Fraction as F
from model import model, HC
c=F(5025,65536); r=F(75,65536); lo=F(2475,32768); hi=F(1275,16384)
m=model(c,r,lo,hi)
def q(x):
    x=F(x)
    if x.denominator==1: return f"({x.numerator} : ℝ)" if x>=0 else f"(({x.numerator}) : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)" if x>=0 else f"((-{-x.numerator}) / {x.denominator} : ℝ)"
def qq(x):
    x=F(x); return f"{x.numerator}" if x.denominator==1 else f"{x.numerator}/{x.denominator}"
G=m['G']; B=m['B']
floor_minus=m['floor']-m['err']
L=F(int(floor_minus*10**12)-1,10**12)
epsH=F(int(m['epsH']*10**15)+1,10**15)   # rational upper bound
epsW=F(1,10**19)
HB=F(int(m['HB'])+1); EB=F(int(m['EB'])+1)
NS="AEGIS.RHKreinFifteenthCellDirectCorrectionV1"
o=[]
w=o.append
w(f"""/-
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

import AEGISOverlay.RHKreinExplicitCorrectionV1
import AEGISOverlay.RHKreinFiniteIntervalKernelV1

/-!
# Fifteenth-cell direct correction lower bound (derivative-free)

For every `t` in serialized cell index 14, `[2475/32768, 1275/16384]`, the exact
correction symbol is bounded below by an explicit rational.  The proof expands
`cos ((c + s) h) = cos (c h) cos (s h) - sin (c h) sin (s h)` around the cell
center `c = 5025/65536`, encloses `cos (c h)` and `sin (c h)` by degree-fifteen
Taylor polynomials rounded to `10^-24`, encloses `cos (s h)`, `sin (s h)`,
and both `sinc` factors by low-degree polynomials with explicit remainders,
and finishes with a sign-independent floor of one degree-thirteen rational
polynomial in `s = t - c`.  No derivative of the correction symbol and no M8
remainder is used.

No cell-soundness, all-cells, or RH statement is concluded here.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 65536
noncomputable section

namespace {NS}

open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open scoped BigOperators

def c15 : ℝ := 5025 / 65536
def r15 : ℝ := 75 / 65536

/-! ## Generic primitives -/

def cP (y : ℝ) : ℝ := 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720
def sP (y : ℝ) : ℝ := y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040

def cosPolynomial15 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
    x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 -
      x ^ 14 / 87178291200

def sinPolynomial15 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
    x ^ 9 / 362880 - x ^ 11 / 39916800 + x ^ 13 / 6227020800 -
      x ^ 15 / 1307674368000

theorem expIPartial_eight_re (x : ℝ) : (expIPartial 8 x).re = cP x := by
  norm_num [expIPartial, cP, Finset.sum_range_succ, pow_succ, Complex.mul_re]
  ring

theorem expIPartial_eight_im (x : ℝ) : (expIPartial 8 x).im = sP x := by
  norm_num [expIPartial, sP, Finset.sum_range_succ, pow_succ, Complex.mul_im]
  ring

theorem expIPartial_sixteen_re (x : ℝ) :
    (expIPartial 16 x).re = cosPolynomial15 x := by
  norm_num [expIPartial, cosPolynomial15, Finset.sum_range_succ,
    pow_succ, Complex.mul_re]
  ring

theorem expIPartial_sixteen_im (x : ℝ) :
    (expIPartial 16 x).im = sinPolynomial15 x := by
  norm_num [expIPartial, sinPolynomial15, Finset.sum_range_succ,
    pow_succ, Complex.mul_im]
  ring

private theorem eight_const_le (y : ℝ) (hy : |y| ≤ 1 / 100) :
    |y| ^ 8 * (((Nat.succ 8 : ℕ) : ℝ) * ((Nat.factorial 8 : ℕ) * 8 : ℝ)⁻¹) ≤
      1 / 100000000000000000000 := by
  have hp := pow_le_pow_left₀ (abs_nonneg y) hy 8
  calc
    |y| ^ 8 * (((Nat.succ 8 : ℕ) : ℝ) * ((Nat.factorial 8 : ℕ) * 8 : ℝ)⁻¹) ≤
        (1 / 100) ^ 8 * (((Nat.succ 8 : ℕ) : ℝ) * ((Nat.factorial 8 : ℕ) * 8 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ 1 / 100000000000000000000 := by norm_num

theorem cos_small (y : ℝ) (hy : |y| ≤ 1 / 100) :
    |Real.cos y - cP y| ≤ 1 / 100000000000000000000 := by
  have h := cos_expIPartial_error 8 y (by norm_num) (hy.trans (by norm_num))
  rw [expIPartial_eight_re] at h
  exact h.trans (eight_const_le y hy)

theorem sin_small (y : ℝ) (hy : |y| ≤ 1 / 100) :
    |Real.sin y - sP y| ≤ 1 / 100000000000000000000 := by
  have h := sin_expIPartial_error 8 y (by norm_num) (hy.trans (by norm_num))
  rw [expIPartial_eight_im] at h
  exact h.trans (eight_const_le y hy)

theorem cP_abs_le (y : ℝ) (hy : |y| ≤ 1 / 100) : |cP y| ≤ 2 := by
  have h1 := Real.abs_cos_le_one y
  have h2 := cos_small y hy
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem sP_abs_le (y : ℝ) (hy : |y| ≤ 1 / 100) : |sP y| ≤ 2 := by
  have h1 := Real.abs_sin_le_one y
  have h2 := sin_small y hy
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_mul_le_of {{x y X Y : ℝ}} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- Addition-formula enclosure for `cos (a + b)` with small `b`. -/
theorem cos_add_approx (a b Q R : ℝ) (hb : |b| ≤ 1 / 100) :
    |Real.cos (a + b) - (Q * cP b - R * sP b)| ≤
      2 / 100000000000000000000 + 2 * |Real.cos a - Q| + 2 * |Real.sin a - R| := by
  have p1 := abs_mul_le_of (Real.abs_cos_le_one a) (cos_small b hb)
  have p2 := abs_mul_le_of (le_refl |Real.cos a - Q|) (cP_abs_le b hb)
  have p3 := abs_mul_le_of (Real.abs_sin_le_one a) (sin_small b hb)
  have p4 := abs_mul_le_of (le_refl |Real.sin a - R|) (sP_abs_le b hb)
  have e : Real.cos (a + b) - (Q * cP b - R * sP b) =
      Real.cos a * (Real.cos b - cP b) + (Real.cos a - Q) * cP b -
        (Real.sin a * (Real.sin b - sP b) + (Real.sin a - R) * sP b) := by
    rw [Real.cos_add]; ring
  rw [e, abs_le]
  constructor <;>
    linarith [neg_abs_le (Real.cos a * (Real.cos b - cP b)),
      le_abs_self (Real.cos a * (Real.cos b - cP b)),
      neg_abs_le ((Real.cos a - Q) * cP b), le_abs_self ((Real.cos a - Q) * cP b),
      neg_abs_le (Real.sin a * (Real.sin b - sP b)),
      le_abs_self (Real.sin a * (Real.sin b - sP b)),
      neg_abs_le ((Real.sin a - R) * sP b), le_abs_self ((Real.sin a - R) * sP b)]

/-- Addition-formula enclosure for `sin (a + b)` with small `b`. -/
theorem sin_add_approx (a b Q R : ℝ) (hb : |b| ≤ 1 / 100) :
    |Real.sin (a + b) - (R * cP b + Q * sP b)| ≤
      2 / 100000000000000000000 + 2 * |Real.sin a - R| + 2 * |Real.cos a - Q| := by
  have p1 := abs_mul_le_of (Real.abs_sin_le_one a) (cos_small b hb)
  have p2 := abs_mul_le_of (le_refl |Real.sin a - R|) (cP_abs_le b hb)
  have p3 := abs_mul_le_of (Real.abs_cos_le_one a) (sin_small b hb)
  have p4 := abs_mul_le_of (le_refl |Real.cos a - Q|) (sP_abs_le b hb)
  have e : Real.sin (a + b) - (R * cP b + Q * sP b) =
      Real.sin a * (Real.cos b - cP b) + (Real.sin a - R) * cP b +
        (Real.cos a * (Real.sin b - sP b) + (Real.cos a - Q) * sP b) := by
    rw [Real.sin_add]; ring
  rw [e, abs_le]
  constructor <;>
    linarith [neg_abs_le (Real.sin a * (Real.cos b - cP b)),
      le_abs_self (Real.sin a * (Real.cos b - cP b)),
      neg_abs_le ((Real.sin a - R) * cP b), le_abs_self ((Real.sin a - R) * cP b),
      neg_abs_le (Real.cos a * (Real.sin b - sP b)),
      le_abs_self (Real.cos a * (Real.sin b - sP b)),
      neg_abs_le ((Real.cos a - Q) * sP b), le_abs_self ((Real.cos a - Q) * sP b)]

/-- Degree-fifteen enclosure of `cos` and `sin` on `|x| ≤ 3/8`. -/
theorem cos15_err (x : ℝ) (hx : |x| ≤ 3 / 8) :
    |Real.cos x - cosPolynomial15 x| ≤ 1 / 100000000000000000000 := by
  have h := cos_expIPartial_error 16 x (by norm_num) (hx.trans (by norm_num))
  rw [expIPartial_sixteen_re] at h
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 16
  refine h.trans ?_
  calc
    |x| ^ 16 * (((Nat.succ 16 : ℕ) : ℝ) * ((Nat.factorial 16 : ℕ) * 16 : ℝ)⁻¹) ≤
        (3 / 8 : ℝ) ^ 16 * (((Nat.succ 16 : ℕ) : ℝ) *
          ((Nat.factorial 16 : ℕ) * 16 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ 1 / 100000000000000000000 := by norm_num

theorem sin15_err (x : ℝ) (hx : |x| ≤ 3 / 8) :
    |Real.sin x - sinPolynomial15 x| ≤ 1 / 100000000000000000000 := by
  have h := sin_expIPartial_error 16 x (by norm_num) (hx.trans (by norm_num))
  rw [expIPartial_sixteen_im] at h
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 16
  refine h.trans ?_
  calc
    |x| ^ 16 * (((Nat.succ 16 : ℕ) : ℝ) * ((Nat.factorial 16 : ℕ) * 16 : ℝ)⁻¹) ≤
        (3 / 8 : ℝ) ^ 16 * (((Nat.succ 16 : ℕ) : ℝ) *
          ((Nat.factorial 16 : ℕ) * 16 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ 1 / 100000000000000000000 := by norm_num

/-- `sinc x = 1 - x²/6 + O(x⁴)` with an explicit constant, for small positive `x`. -/
theorem sinc_quad (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 1 / 1000) :
    |Real.sinc x - (1 - x ^ 2 / 6)| ≤ x ^ 4 / 100 := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_pos hx0]; linarith
  have hsin := sin_expIPartial_error 8 x (by norm_num) hx1
  rw [expIPartial_eight_im, abs_of_pos hx0] at hsin
  have hk : x ^ 8 * (((Nat.succ 8 : ℕ) : ℝ) * ((Nat.factorial 8 : ℕ) * 8 : ℝ)⁻¹) ≤
      x ^ 8 / 10000 := by
    have : (((Nat.succ 8 : ℕ) : ℝ) * ((Nat.factorial 8 : ℕ) * 8 : ℝ)⁻¹) ≤ 1 / 10000 := by
      norm_num
    calc _ ≤ x ^ 8 * (1 / 10000) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = x ^ 8 / 10000 := by ring
  rw [Real.sinc_of_ne_zero hx0.ne']
  have key : Real.sin x / x - (1 - x ^ 2 / 6) =
      (Real.sin x - sP x) / x + (x ^ 4 / 120 - x ^ 6 / 5040) := by
    unfold sP; field_simp; ring
  rw [key]
  have h1 : |(Real.sin x - sP x) / x| ≤ x ^ 7 / 10000 := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc |Real.sin x - sP x| ≤ x ^ 8 / 10000 := hsin.trans hk
      _ = x ^ 7 / 10000 * x := by ring
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ 1 := by nlinarith
  have h4 : 0 ≤ x ^ 4 := by positivity
  have h6 : x ^ 6 ≤ x ^ 4 := by
    calc x ^ 6 = x ^ 4 * x ^ 2 := by ring
      _ ≤ x ^ 4 * 1 := mul_le_mul_of_nonneg_left hx2 h4
      _ = x ^ 4 := by ring
  have h7 : x ^ 7 ≤ x ^ 4 := by
    calc x ^ 7 = x ^ 4 * x ^ 3 := by ring
      _ ≤ x ^ 4 * 1 := mul_le_mul_of_nonneg_left hx3 h4
      _ = x ^ 4 := by ring
  have h60 : 0 ≤ x ^ 6 := by positivity
  have h2 : |x ^ 4 / 120 - x ^ 6 / 5040| ≤ x ^ 4 / 120 := by
    rw [abs_le]; constructor <;> linarith
  calc
    |(Real.sin x - sP x) / x + (x ^ 4 / 120 - x ^ 6 / 5040)| ≤
        |(Real.sin x - sP x) / x| + |x ^ 4 / 120 - x ^ 6 / 5040| := abs_add_le _ _
    _ ≤ x ^ 7 / 10000 + x ^ 4 / 120 := add_le_add h1 h2
    _ ≤ x ^ 4 / 100 := by linarith

theorem one_sub_pow_upper (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∀ m : ℕ, (1 - v) ^ m ≤ 1 - (m : ℝ) * v + (m : ℝ) ^ 2 * v ^ 2 / 2
  | 0 => by simp
  | m + 1 => by
    have ih := one_sub_pow_upper v hv0 hv1 m
    have h1v : 0 ≤ 1 - v := by linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [pow_succ]
    calc (1 - v) ^ m * (1 - v) ≤
          (1 - (m : ℝ) * v + (m : ℝ) ^ 2 * v ^ 2 / 2) * (1 - v) :=
        mul_le_mul_of_nonneg_right ih h1v
      _ ≤ 1 - ((m + 1 : ℕ) : ℝ) * v + ((m + 1 : ℕ) : ℝ) ^ 2 * v ^ 2 / 2 := by
        push_cast
        nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg (m : ℝ)) (pow_nonneg hv0 3)]

theorem one_sub_pow_lower (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * v ≤ (1 - v) ^ m := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -v by linarith) m
  simpa [sub_eq_add_neg, mul_neg] using h

theorem pow_quad (u v ε : ℝ) (m : ℕ) (hu : |u| ≤ 1)
    (huv : |u - (1 - v)| ≤ ε) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |u ^ m - (1 - (m : ℝ) * v)| ≤ (m : ℝ) * ε + (m : ℝ) ^ 2 * v ^ 2 / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans huv
  have h1 := abs_pow_sub_pow_le u (1 - v) m
  have hmax : max |u| |1 - v| ≤ 1 :=
    max_le hu (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hpow : max |u| |1 - v| ^ (m - 1) ≤ 1 :=
    pow_le_one₀ ((abs_nonneg _).trans (le_max_left _ _)) hmax
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 : |u ^ m - (1 - v) ^ m| ≤ ε * m := by
    calc |u ^ m - (1 - v) ^ m| ≤ |u - (1 - v)| * m * max |u| |1 - v| ^ (m - 1) := h1
      _ ≤ ε * m * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right huv hm) hpow
          (pow_nonneg ((abs_nonneg _).trans (le_max_left _ _)) _)
        positivity
      _ = ε * m := by ring
  have h3 := one_sub_pow_upper v hv0 hv1 m
  have h4 := one_sub_pow_lower v hv0 hv1 m
  rw [abs_le] at h2 ⊢
  constructor <;> nlinarith [h2.1, h2.2]

theorem term_lower (g s r : ℝ) (k : ℕ) (hs : |s| ≤ r) :
    -(|g| * r ^ k) ≤ g * s ^ k := by
  have hp : |s| ^ k ≤ r ^ k := pow_le_pow_left₀ (abs_nonneg s) hs k
  have h : |g * s ^ k| ≤ |g| * r ^ k := by
    rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg g)
  linarith [neg_abs_le (g * s ^ k)]

/-! ## Rounded center tables -/
""")
def table(name, vals):
    return f"def {name} : Fin 199 → ℚ :=\n  ![" + ",\n    ".join(qq(v) for v in vals) + "]\n"
w(table("hatCosQ", m['Q'])); w(table("hatSinQ", m['R']))
w(f"""
def edgeCosQ : ℝ := {q(m['Qw'])}
def edgeSinQ : ℝ := {q(m['Rw'])}

/-! ## Hat sum -/

def hatApprox (s : ℝ) : ℝ :=
  ∑ j : Fin 199, (hatCoefficient j : ℝ) *
    ((hatCosQ j : ℝ) * cP (s * hatCenter j) - (hatSinQ j : ℝ) * sP (s * hatCenter j))

theorem hatCenter_bounds (j : Fin 199) : 0 ≤ hatCenter j ∧ hatCenter j ≤ 239 / 50 := by
  have hjNat : j.val ≤ 198 := by omega
  have hj : (j.val : ℝ) ≤ 198 := by exact_mod_cast hjNat
  unfold hatCenter
  constructor
  · positivity
  · rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith

theorem hat_term_error (j : Fin 199) (s : ℝ) (hs : |s| ≤ r15) :
    |Real.cos ((c15 + s) * hatCenter j) -
        ((hatCosQ j : ℝ) * cP (s * hatCenter j) - (hatSinQ j : ℝ) * sP (s * hatCenter j))| ≤
      6 / 100000000000000000000 +
        2 * |cosPolynomial15 (c15 * hatCenter j) - (hatCosQ j : ℝ)| +
        2 * |sinPolynomial15 (c15 * hatCenter j) - (hatSinQ j : ℝ)| := by
  obtain ⟨h0, h1⟩ := hatCenter_bounds j
  have hb : |s * hatCenter j| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg h0]
    calc |s| * hatCenter j ≤ r15 * (239 / 50) :=
          mul_le_mul hs h1 h0 ((abs_nonneg s).trans hs)
      _ ≤ 1 / 100 := by norm_num [r15]
  have hx : |c15 * hatCenter j| ≤ 3 / 8 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num [c15]) h0)]
    calc c15 * hatCenter j ≤ c15 * (239 / 50) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num [c15])
      _ ≤ 3 / 8 := by norm_num [c15]
  have e : (c15 + s) * hatCenter j = c15 * hatCenter j + s * hatCenter j := by ring
  rw [e]
  have h := cos_add_approx (c15 * hatCenter j) (s * hatCenter j) (hatCosQ j) (hatSinQ j) hb
  have hc := cos15_err _ hx
  have hsn := sin15_err _ hx
  have tc : |Real.cos (c15 * hatCenter j) - (hatCosQ j : ℝ)| ≤
      1 / 100000000000000000000 + |cosPolynomial15 (c15 * hatCenter j) - (hatCosQ j : ℝ)| := by
    have := abs_sub_le (Real.cos (c15 * hatCenter j)) (cosPolynomial15 (c15 * hatCenter j))
      (hatCosQ j : ℝ)
    linarith
  have ts : |Real.sin (c15 * hatCenter j) - (hatSinQ j : ℝ)| ≤
      1 / 100000000000000000000 + |sinPolynomial15 (c15 * hatCenter j) - (hatSinQ j : ℝ)| := by
    have := abs_sub_le (Real.sin (c15 * hatCenter j)) (sinPolynomial15 (c15 * hatCenter j))
      (hatSinQ j : ℝ)
    linarith
  linarith

def hatTableError : ℝ :=
  ∑ j : Fin 199, |(hatCoefficient j : ℝ)| *
    (6 / 100000000000000000000 +
      2 * |cosPolynomial15 (c15 * hatCenter j) - (hatCosQ j : ℝ)| +
      2 * |sinPolynomial15 (c15 * hatCenter j) - (hatSinQ j : ℝ)|)

theorem hatTableError_le : hatTableError ≤ {q(epsH)} := by
  norm_num (config := {{ maxSteps := 200000000 }}) [hatTableError, cosPolynomial15, sinPolynomial15, c15, hatCenter,
    hatCoefficient, hatCosQ, hatSinQ, Fin.sum_univ_succ]

theorem hat_sum_error (s : ℝ) (hs : |s| ≤ r15) :
    |(∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos ((c15 + s) * hatCenter j)) -
        hatApprox s| ≤ {q(epsH)} := by
  refine le_trans ?_ hatTableError_le
  unfold hatApprox hatTableError
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hat_term_error j s hs) (abs_nonneg _)

theorem hat_abs_le (t : ℝ) :
    |∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)| ≤ {q(HB)} := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin 199, |(hatCoefficient j : ℝ) * Real.cos (t * hatCenter j)| ≤
        ∑ j : Fin 199, |(hatCoefficient j : ℝ)| := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        calc |(hatCoefficient j : ℝ)| * |Real.cos (t * hatCenter j)| ≤
            |(hatCoefficient j : ℝ)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = _ := by ring
    _ ≤ {q(HB)} := by norm_num [hatCoefficient, Fin.sum_univ_succ]
""")
# hat polynomial identity
coef_names=[]
terms=[]
def gam_expr(k):
    # coefficient expression per j of s^k
    cj="(hatCoefficient j : ℝ)"; Qj="(hatCosQ j : ℝ)"; Rj="(hatSinQ j : ℝ)"; h="hatCenter j"
    from math import factorial
    sgn=(-1)**(k//2)
    base = Qj if k%2==0 else Rj
    s = sgn if k%2==0 else -sgn
    sign = "" if s>0 else "-"
    return f"({sign}({cj} * {base} * {h} ^ {k} / {factorial(k)}))"
w("theorem hatApprox_poly (s : ℝ) :\n    hatApprox s =\n      " + " +\n      ".join(f"{q(B[k])} * s ^ {k}" for k in range(8)) + " := by")
w("  have hj : ∀ j : Fin 199, (hatCoefficient j : ℝ) *\n      ((hatCosQ j : ℝ) * cP (s * hatCenter j) - (hatSinQ j : ℝ) * sP (s * hatCenter j)) =\n      " + " +\n      ".join(f"{gam_expr(k)} * s ^ {k}" for k in range(8)) + " := by\n    intro j; unfold cP sP; ring")
w("  unfold hatApprox\n  rw [Finset.sum_congr rfl (fun j _ => hj j)]\n  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]")
for k in range(8):
    w(f"  have e{k} : (∑ j : Fin 199, {gam_expr(k)}) = {q(B[k])} := by\n    norm_num [hatCoefficient, hatCosQ, hatSinQ, hatCenter, Fin.sum_univ_succ]")
w("  rw [" + ", ".join(f"e{k}" for k in range(8)) + "]\n")
# edge
w(f"""
/-! ## Edge sum -/

def edgeW : ℝ := 1619 / 2000

def edgePc (s : ℝ) : ℝ := edgeCosQ * cP (s * edgeW) - edgeSinQ * sP (s * edgeW)
def edgePs (s : ℝ) : ℝ := edgeSinQ * cP (s * edgeW) + edgeCosQ * sP (s * edgeW)

def edgeApprox (s : ℝ) : ℝ :=
  (splineCoefficient 0 : ℝ) * edgePc s +
    (splineCoefficient 1 : ℝ) * (c15 + s) * edgePs s +
    (splineCoefficient 2 : ℝ) * (c15 + s) ^ 2 * edgePc s +
    (splineCoefficient 3 : ℝ) * (c15 + s) ^ 3 * edgePs s +
    (splineCoefficient 4 : ℝ) * (c15 + s) ^ 4 * edgePc s

def edgePhaseError : ℝ :=
  6 / 100000000000000000000 + 2 * |cosPolynomial15 (c15 * edgeW) - edgeCosQ| +
    2 * |sinPolynomial15 (c15 * edgeW) - edgeSinQ|

theorem edgePhaseError_le : edgePhaseError ≤ {q(epsW)} := by
  norm_num [edgePhaseError, cosPolynomial15, sinPolynomial15, c15, edgeW, edgeCosQ, edgeSinQ]

theorem edge_phase_bounds (s : ℝ) (hs : |s| ≤ r15) :
    |Real.cos ((c15 + s) * (1619 / 2000)) - edgePc s| ≤ {q(epsW)} ∧
      |Real.sin ((c15 + s) * (1619 / 2000)) - edgePs s| ≤ {q(epsW)} := by
  have hb : |s * edgeW| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg (by norm_num [edgeW] : (0 : ℝ) ≤ edgeW)]
    calc |s| * edgeW ≤ r15 * edgeW :=
          mul_le_mul_of_nonneg_right hs (by norm_num [edgeW])
      _ ≤ 1 / 100 := by norm_num [r15, edgeW]
  have hx : |c15 * edgeW| ≤ 3 / 8 := by norm_num [c15, edgeW, abs_of_nonneg]
  have e : (c15 + s) * (1619 / 2000) = c15 * edgeW + s * edgeW := by unfold edgeW; ring
  have hc := cos15_err _ hx
  have hsn := sin15_err _ hx
  have tc : |Real.cos (c15 * edgeW) - edgeCosQ| ≤
      1 / 100000000000000000000 + |cosPolynomial15 (c15 * edgeW) - edgeCosQ| := by
    have := abs_sub_le (Real.cos (c15 * edgeW)) (cosPolynomial15 (c15 * edgeW)) edgeCosQ
    linarith
  have ts : |Real.sin (c15 * edgeW) - edgeSinQ| ≤
      1 / 100000000000000000000 + |sinPolynomial15 (c15 * edgeW) - edgeSinQ| := by
    have := abs_sub_le (Real.sin (c15 * edgeW)) (sinPolynomial15 (c15 * edgeW)) edgeSinQ
    linarith
  have hE := edgePhaseError_le
  unfold edgePhaseError at hE
  rw [e]
  constructor
  · have h := cos_add_approx (c15 * edgeW) (s * edgeW) edgeCosQ edgeSinQ hb
    unfold edgePc; linarith
  · have h := sin_add_approx (c15 * edgeW) (s * edgeW) edgeCosQ edgeSinQ hb
    unfold edgePs; linarith

theorem edge_expand (t : ℝ) :
    (∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000)))) =
    (splineCoefficient 0 : ℝ) * Real.cos (t * (1619 / 2000)) +
      (splineCoefficient 1 : ℝ) * t * Real.sin (t * (1619 / 2000)) +
      (splineCoefficient 2 : ℝ) * t ^ 2 * Real.cos (t * (1619 / 2000)) +
      (splineCoefficient 3 : ℝ) * t ^ 3 * Real.sin (t * (1619 / 2000)) +
      (splineCoefficient 4 : ℝ) * t ^ 4 * Real.cos (t * (1619 / 2000)) := by
  simp [Fin.sum_univ_five]

theorem spl0 : splineCoefficient 0 = 234102120892757/5000000000 := rfl
theorem spl1 : splineCoefficient 1 = -12240399939171/2500000000 := rfl
theorem spl2 : splineCoefficient 2 = -2918648959121/10000000000 := rfl
theorem spl3 : splineCoefficient 3 = 123578990441/10000000000 := rfl
theorem spl4 : splineCoefficient 4 = 9711997751/10000000000 := rfl

theorem spline_abs :
    |(splineCoefficient 0 : ℝ)| + |(splineCoefficient 1 : ℝ)| + |(splineCoefficient 2 : ℝ)| +
      |(splineCoefficient 3 : ℝ)| + |(splineCoefficient 4 : ℝ)| ≤ {q(EB)} := by
  rw [spl0, spl1, spl2, spl3, spl4]
  norm_num

theorem edge_sum_error (s : ℝ) (hs : |s| ≤ r15) (ht0 : 0 ≤ c15 + s) (ht1 : c15 + s ≤ 1) :
    |(∑ j : Fin 5, (splineCoefficient j : ℝ) * (c15 + s) ^ j.val *
      (if j.val % 2 = 0 then Real.cos ((c15 + s) * (1619 / 2000))
       else Real.sin ((c15 + s) * (1619 / 2000)))) - edgeApprox s| ≤ {q(EB)} * {q(epsW)} := by
  rw [edge_expand]
  obtain ⟨hc, hsn⟩ := edge_phase_bounds s hs
  set t := c15 + s
  have p1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have pw (k : ℕ) : |t ^ k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) p1
  have b0 := abs_mul_le_of (le_refl |(splineCoefficient 0 : ℝ)|) hc
  have b1 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 1 : ℝ)|) (pw 1)) hsn
  have b2 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 2 : ℝ)|) (pw 2)) hc
  have b3 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 3 : ℝ)|) (pw 3)) hsn
  have b4 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 4 : ℝ)|) (pw 4)) hc
  simp only [pow_one] at b1
  have hsp := spline_abs
  have e : (splineCoefficient 0 : ℝ) * Real.cos (t * (1619 / 2000)) +
      (splineCoefficient 1 : ℝ) * t * Real.sin (t * (1619 / 2000)) +
      (splineCoefficient 2 : ℝ) * t ^ 2 * Real.cos (t * (1619 / 2000)) +
      (splineCoefficient 3 : ℝ) * t ^ 3 * Real.sin (t * (1619 / 2000)) +
      (splineCoefficient 4 : ℝ) * t ^ 4 * Real.cos (t * (1619 / 2000)) - edgeApprox s =
      (splineCoefficient 0 : ℝ) * (Real.cos (t * (1619 / 2000)) - edgePc s) +
      (splineCoefficient 1 : ℝ) * t * (Real.sin (t * (1619 / 2000)) - edgePs s) +
      (splineCoefficient 2 : ℝ) * t ^ 2 * (Real.cos (t * (1619 / 2000)) - edgePc s) +
      (splineCoefficient 3 : ℝ) * t ^ 3 * (Real.sin (t * (1619 / 2000)) - edgePs s) +
      (splineCoefficient 4 : ℝ) * t ^ 4 * (Real.cos (t * (1619 / 2000)) - edgePc s) := by
    unfold edgeApprox; ring
  rw [e]
  have a0 := abs_nonneg ((splineCoefficient 0 : ℝ))
  have a1 := abs_nonneg ((splineCoefficient 1 : ℝ))
  have a2 := abs_nonneg ((splineCoefficient 2 : ℝ))
  have a3 := abs_nonneg ((splineCoefficient 3 : ℝ))
  have a4 := abs_nonneg ((splineCoefficient 4 : ℝ))
  rw [abs_le]
  constructor <;> nlinarith [neg_abs_le ((splineCoefficient 0 : ℝ) * (Real.cos (t * (1619 / 2000)) - edgePc s)),
      le_abs_self ((splineCoefficient 0 : ℝ) * (Real.cos (t * (1619 / 2000)) - edgePc s)),
      neg_abs_le ((splineCoefficient 1 : ℝ) * t * (Real.sin (t * (1619 / 2000)) - edgePs s)),
      le_abs_self ((splineCoefficient 1 : ℝ) * t * (Real.sin (t * (1619 / 2000)) - edgePs s)),
      neg_abs_le ((splineCoefficient 2 : ℝ) * t ^ 2 * (Real.cos (t * (1619 / 2000)) - edgePc s)),
      le_abs_self ((splineCoefficient 2 : ℝ) * t ^ 2 * (Real.cos (t * (1619 / 2000)) - edgePc s)),
      neg_abs_le ((splineCoefficient 3 : ℝ) * t ^ 3 * (Real.sin (t * (1619 / 2000)) - edgePs s)),
      le_abs_self ((splineCoefficient 3 : ℝ) * t ^ 3 * (Real.sin (t * (1619 / 2000)) - edgePs s)),
      neg_abs_le ((splineCoefficient 4 : ℝ) * t ^ 4 * (Real.cos (t * (1619 / 2000)) - edgePc s)),
      le_abs_self ((splineCoefficient 4 : ℝ) * t ^ 4 * (Real.cos (t * (1619 / 2000)) - edgePc s))]

theorem edge_abs_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000)))| ≤ {q(EB)} := by
  rw [edge_expand]
  have p1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have pw (k : ℕ) : |t ^ k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) p1
  have hc := Real.abs_cos_le_one (t * (1619 / 2000))
  have hsn := Real.abs_sin_le_one (t * (1619 / 2000))
  have b0 := abs_mul_le_of (le_refl |(splineCoefficient 0 : ℝ)|) hc
  have b1 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 1 : ℝ)|) (pw 1)) hsn
  have b2 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 2 : ℝ)|) (pw 2)) hc
  have b3 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 3 : ℝ)|) (pw 3)) hsn
  have b4 := abs_mul_le_of (abs_mul_le_of (le_refl |(splineCoefficient 4 : ℝ)|) (pw 4)) hc
  simp only [pow_one] at b1
  have hsp := spline_abs
  rw [abs_le]
  constructor <;> linarith [neg_abs_le ((splineCoefficient 0 : ℝ) * Real.cos (t * (1619 / 2000))),
      le_abs_self ((splineCoefficient 0 : ℝ) * Real.cos (t * (1619 / 2000))),
      neg_abs_le ((splineCoefficient 1 : ℝ) * t * Real.sin (t * (1619 / 2000))),
      le_abs_self ((splineCoefficient 1 : ℝ) * t * Real.sin (t * (1619 / 2000))),
      neg_abs_le ((splineCoefficient 2 : ℝ) * t ^ 2 * Real.cos (t * (1619 / 2000))),
      le_abs_self ((splineCoefficient 2 : ℝ) * t ^ 2 * Real.cos (t * (1619 / 2000))),
      neg_abs_le ((splineCoefficient 3 : ℝ) * t ^ 3 * Real.sin (t * (1619 / 2000))),
      le_abs_self ((splineCoefficient 3 : ℝ) * t ^ 3 * Real.sin (t * (1619 / 2000))),
      neg_abs_le ((splineCoefficient 4 : ℝ) * t ^ 4 * Real.cos (t * (1619 / 2000))),
      le_abs_self ((splineCoefficient 4 : ℝ) * t ^ 4 * Real.cos (t * (1619 / 2000)))]
""")
# final polynomial
gpoly=" + ".join(f"{q(G[k])} * s ^ {k}" for k in range(len(G)))
w(f"""
/-! ## Assembly -/

def A1 (s : ℝ) : ℝ := 1 - (c15 + s) ^ 2 / 30000
def A2 (s : ℝ) : ℝ := 1 - 19 * (c15 + s) ^ 2 / 24000000

theorem G_poly (s : ℝ) :
    (2 / 50) * A1 s * ({ " + ".join(f"{q(B[k])} * s ^ {k}" for k in range(8)) }) +
      A2 s * edgeApprox s =
    {gpoly} := by
  unfold A1 A2 edgeApprox edgePc edgePs cP sP edgeCosQ edgeSinQ edgeW c15
  rw [spl0, spl1, spl2, spl3, spl4]
  push_cast
  ring

def directLower : ℝ := {q(L)}

theorem correction_lower_direct (t : ℝ) (hlo : (2475 / 32768 : ℝ) ≤ t)
    (hhi : t ≤ (1275 / 16384 : ℝ)) :
    directLower ≤ correctionSymbol t := by
  set s := t - c15 with hsdef
  have ht : t = c15 + s := by rw [hsdef]; ring
  have hs : |s| ≤ r15 := by
    rw [abs_le]; constructor <;> (rw [hsdef]; unfold c15 r15; linarith)
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  -- sinc factors
  have hx0 : 0 < t / 100 := by positivity
  have hx1 : t / 100 ≤ 1 / 1000 := by linarith
  have hy0 : 0 < t / 2000 := by positivity
  have hy1 : t / 2000 ≤ 1 / 20000 := by linarith
  have hS1q := sinc_quad (t / 100) hx0 hx1
  have hS2q := sinc_quad (t / 2000) hy0 (by linarith)
  have hv1 : (t / 100) ^ 2 / 6 ≤ 1 := by nlinarith
  have hv2 : (t / 2000) ^ 2 / 6 ≤ 1 := by nlinarith
  have hS1 := pow_quad (Real.sinc (t / 100)) ((t / 100) ^ 2 / 6) ((t / 100) ^ 4 / 100) 2
    (Real.abs_sinc_le_one _) hS1q (by positivity) hv1
  have hS2 := pow_quad (Real.sinc (t / 2000)) ((t / 2000) ^ 2 / 6) ((t / 2000) ^ 4 / 100) 19
    (Real.abs_sinc_le_one _) hS2q (by positivity) hv2
  have hx4 : (t / 100) ^ 4 ≤ 1 / 1000000000000 := by
    have := pow_le_pow_left₀ hx0.le hx1 4; norm_num at this ⊢; linarith
  have hy4 : (t / 2000) ^ 4 ≤ 1 / 160000000000000000 := by
    have := pow_le_pow_left₀ hy0.le hy1 4; norm_num at this ⊢; linarith
  have hS1' : |Real.sinc (t / 100) ^ 2 - A1 s| ≤ 8 / 100000000000000 := by
    have e : A1 s = 1 - ((2 : ℕ) : ℝ) * ((t / 100) ^ 2 / 6) := by
      unfold A1; rw [← ht]; push_cast; ring
    rw [e]; refine hS1.trans ?_; push_cast
    have : ((t / 100) ^ 2 / 6) ^ 2 = (t / 100) ^ 4 / 36 := by ring
    rw [this]; linarith
  have hS2' : |Real.sinc (t / 2000) ^ 19 - A2 s| ≤ 4 / 100000000000000000 := by
    have e : A2 s = 1 - ((19 : ℕ) : ℝ) * ((t / 2000) ^ 2 / 6) := by
      unfold A2; rw [← ht]; push_cast; ring
    rw [e]; refine hS2.trans ?_; push_cast
    have : ((t / 2000) ^ 2 / 6) ^ 2 = (t / 2000) ^ 4 / 36 := by ring
    rw [this]; linarith
  have hA1 : |A1 s| ≤ 1 := by
    unfold A1; rw [← ht, abs_le]; constructor <;> nlinarith
  have hA2 : |A2 s| ≤ 1 := by
    unfold A2; rw [← ht, abs_le]; constructor <;> nlinarith
  -- sums
  have hH := hat_sum_error s hs
  have hHB := hat_abs_le t
  have hE := edge_sum_error s hs (by rw [← ht]; exact ht0) (by rw [← ht]; exact ht1)
  have hEB := edge_abs_le t ht0 ht1
  rw [← ht] at hH hE
  rw [hatApprox_poly] at hH
  set H := ∑ j : Fin 199, (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j) with hHdef
  set E := ∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000))) with hEdef
  set P := {" + ".join(f"{q(B[k])} * s ^ {k}" for k in range(8))} with hPdef
  have hcorr : correctionSymbol t =
      (2 / 50) * Real.sinc (t / 100) ^ 2 * H + Real.sinc (t / 2000) ^ 19 * E := by
    unfold correctionSymbol; rfl
  -- product errors
  have m1 := abs_mul_le_of hS1' hHB
  have m2 := abs_mul_le_of hA1 hH
  have m3 := abs_mul_le_of hS2' hEB
  have m4 := abs_mul_le_of hA2 hE
  have split : (2 / 50) * Real.sinc (t / 100) ^ 2 * H + Real.sinc (t / 2000) ^ 19 * E =
      ((2 / 50) * A1 s * P + A2 s * edgeApprox s) +
        (2 / 50) * ((Real.sinc (t / 100) ^ 2 - A1 s) * H + A1 s * (H - P)) +
        ((Real.sinc (t / 2000) ^ 19 - A2 s) * E + A2 s * (E - edgeApprox s)) := by ring
  have hG := G_poly s
""")
# floor terms
for k in range(1,len(G)):
    w(f"  have f{k} := term_lower {q(G[k])} s r15 {k} hs")
w(f"""  have hfloor : directLower + {q(F(2,50))} * ({q(F(8,10**14))} * {q(HB)} + {q(epsH)}) +
      ({q(F(4,10**17))} * {q(EB)} + {q(EB)} * {q(epsW)}) ≤
      {q(G[0])} - ({" + ".join(f"|{q(G[k])}| * r15 ^ {k}" for k in range(1,len(G)))}) := by
    norm_num [directLower, r15]
  rw [hcorr, split, hG]
  rw [abs_le] at m1 m2 m3 m4
  nlinarith [m1.1, m2.1, m3.1, m4.1, {", ".join(f"f{k}" for k in range(1,len(G)))}]

end {NS}

#print axioms {NS}.correction_lower_direct
""")
open(sys.argv[1],'w').write("\n".join(o))
print('L',float(L),'epsH',float(epsH))
