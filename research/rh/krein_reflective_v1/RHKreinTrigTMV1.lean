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

import RHKreinTaylorModelV1
import AEGISOverlay.RHKreinFiniteIntervalKernelV1

/-!
# Trigonometric Taylor models

* `cosSin n k P a`: an enclosure of `(cos a, sin a)` for any rational `a`, by `k` halvings,
  an `n`-term Taylor polynomial, and `k` doublings rounded to `2^-P`.
* `cosAffTM`, `sinAffTM`: Taylor models of `cos ((c + s) h)`, `sin ((c + s) h)` on `|s| ≤ r`.
* `sincAffTM`: Taylor model of `sinc ((c + s) / d)` for `c > r`.

Every constructor falls back to a trivially valid model when its side condition fails, so the
enclosure theorems carry no numerical hypotheses.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinTrigTMV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open Complex

/-! ## Taylor coefficients -/

def cosCoef (m : ℕ) : ℚ := if m % 2 = 0 then (-1) ^ (m / 2) / (m.factorial : ℚ) else 0
def sinCoef (m : ℕ) : ℚ := if m % 2 = 1 then (-1) ^ (m / 2) / (m.factorial : ℚ) else 0

theorem I_pow_eq (m : ℕ) :
    I ^ m = (if m % 2 = 0 then ((-1 : ℂ) ^ (m / 2)) else ((-1 : ℂ) ^ (m / 2)) * I) := by
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' m
  · have h1 : 2 * q % 2 = 0 := by omega
    have h2 : 2 * q / 2 = q := by omega
    rw [if_pos h1, h2, pow_mul, I_sq]
  · have h1 : ¬ (2 * q + 1) % 2 = 0 := by omega
    have h2 : (2 * q + 1) / 2 = q := by omega
    rw [if_neg h1, h2, pow_succ, pow_mul, I_sq]

theorem term_eq (x : ℝ) (m : ℕ) :
    ((x : ℂ) * I) ^ m / (m.factorial : ℂ) = ((x ^ m / m.factorial : ℝ) : ℂ) * I ^ m := by
  push_cast; ring

theorem term_re (x : ℝ) (m : ℕ) :
    (((x : ℂ) * I) ^ m / (m.factorial : ℂ)).re = (cosCoef m : ℝ) * x ^ m := by
  rw [term_eq, I_pow_eq]
  unfold cosCoef
  split_ifs with h
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_mul, ofReal_re]
    push_cast; ring
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl,
      ← mul_assoc, ← ofReal_mul, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
    push_cast; ring

theorem term_im (x : ℝ) (m : ℕ) :
    (((x : ℂ) * I) ^ m / (m.factorial : ℂ)).im = (sinCoef m : ℝ) * x ^ m := by
  rw [term_eq, I_pow_eq]
  unfold sinCoef
  split_ifs with h h'
  · omega
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_mul, ofReal_im]
    simp
  · rw [show ((-1 : ℂ) ^ (m / 2)) = (((-1 : ℝ) ^ (m / 2) : ℝ) : ℂ) by push_cast; rfl,
      ← mul_assoc, ← ofReal_mul, Complex.im_ofReal_mul, Complex.I_im, mul_one]
    push_cast; ring
  · omega

/-- Coefficient list `f k hᵏ, f (k+1) hᵏ⁺¹, …` of length `n`. -/
def coefFrom (f : ℕ → ℚ) (h : ℚ) : ℕ → ℕ → Poly
  | _, 0 => []
  | k, n + 1 => (f k * h ^ k) :: coefFrom f h (k + 1) n

theorem eval_coefFrom (f : ℕ → ℚ) (h : ℚ) (x : ℝ) :
    ∀ (n k : ℕ), eval (coefFrom f h k n) x * x ^ k =
      ∑ m ∈ Finset.range n, (f (k + m) : ℝ) * (h : ℝ) ^ (k + m) * x ^ (k + m)
  | 0, k => by simp [coefFrom]
  | n + 1, k => by
    rw [Finset.sum_range_succ']
    have ih := eval_coefFrom f h x n (k + 1)
    simp only [coefFrom, eval_cons]
    push_cast
    rw [show ∑ m ∈ Finset.range n, (f (k + (m + 1)) : ℝ) * (h : ℝ) ^ (k + (m + 1)) *
        x ^ (k + (m + 1)) =
      ∑ m ∈ Finset.range n, (f (k + 1 + m) : ℝ) * (h : ℝ) ^ (k + 1 + m) * x ^ (k + 1 + m) by
        apply Finset.sum_congr rfl; intro m _; rw [show k + (m + 1) = k + 1 + m by omega]]
    rw [← ih]
    simp only [add_zero]
    ring

theorem eval_coefFrom_zero (f : ℕ → ℚ) (h : ℚ) (x : ℝ) (n : ℕ) :
    eval (coefFrom f h 0 n) x =
      ∑ m ∈ Finset.range n, (f m : ℝ) * ((h : ℝ) * x) ^ m := by
  have := eval_coefFrom f h x n 0
  simp only [pow_zero, mul_one, zero_add] at this
  rw [this]
  apply Finset.sum_congr rfl; intro m _; ring

theorem expIPartial_re_eq (n : ℕ) (x : ℝ) :
    (expIPartial n x).re = eval (coefFrom cosCoef 1 0 n) x := by
  rw [eval_coefFrom_zero]
  unfold expIPartial
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [term_re]; push_cast; ring

theorem expIPartial_im_eq (n : ℕ) (x : ℝ) :
    (expIPartial n x).im = eval (coefFrom sinCoef 1 0 n) x := by
  rw [eval_coefFrom_zero]
  unfold expIPartial
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [term_im]; push_cast; ring

/-- The Lagrange-type constant of `expIPartial_error`. -/
def taylorErr (n : ℕ) (x : ℚ) : ℚ := x ^ n * ((n + 1 : ℚ) / (n.factorial * n))

theorem taylorErr_cast (n : ℕ) (x : ℚ) :
    ((taylorErr n x : ℚ) : ℝ) = (x : ℝ) ^ n * (((n.succ : ℕ) : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  unfold taylorErr; push_cast; ring

/-- `cos (s h)` and `sin (s h)` on `|s| ≤ r`, provided `r |h| ≤ 1`. -/
def cosScaledTM (n : ℕ) (r h : ℚ) : TM :=
  if 0 < n ∧ 0 ≤ r ∧ r * |h| ≤ 1 then ⟨coefFrom cosCoef h 0 n, taylorErr n (r * |h|)⟩
  else ⟨[], 1⟩

def sinScaledTM (n : ℕ) (r h : ℚ) : TM :=
  if 0 < n ∧ 0 ≤ r ∧ r * |h| ≤ 1 then ⟨coefFrom sinCoef h 0 n, taylorErr n (r * |h|)⟩
  else ⟨[], 1⟩

theorem eval_coefFrom_scaled (f : ℕ → ℚ) (h : ℚ) (s : ℝ) (n : ℕ) :
    eval (coefFrom f h 0 n) s = eval (coefFrom f 1 0 n) ((h : ℝ) * s) := by
  rw [eval_coefFrom_zero, eval_coefFrom_zero]
  apply Finset.sum_congr rfl; intro m _; push_cast; ring

theorem taylor_err_mono (n : ℕ) (r h : ℚ) (s : ℝ) (hr : 0 ≤ r) (hs : |s| ≤ r) :
    |(h : ℝ) * s| ^ n * (((n.succ : ℕ) : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤
      ((taylorErr n (r * |h|) : ℚ) : ℝ) := by
  rw [taylorErr_cast]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (abs_nonneg _)
  rw [abs_mul]; push_cast
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

theorem encl_cosScaled (n : ℕ) (r h : ℚ) :
    Encl r (fun s => Real.cos (s * h)) (cosScaledTM n r h) := by
  intro s hs
  unfold cosScaledTM
  split_ifs with hc
  · obtain ⟨hn, hr, hrh⟩ := hc
    have hx : |(h : ℝ) * s| ≤ 1 := by
      rw [abs_mul]
      calc |(h : ℝ)| * |s| ≤ |(h : ℝ)| * r := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ = ((r * |h| : ℚ) : ℝ) := by push_cast; ring
        _ ≤ 1 := by exact_mod_cast hrh
    have e := cos_expIPartial_error n ((h : ℝ) * s) hn hx
    rw [expIPartial_re_eq] at e
    simp only
    rw [eval_coefFrom_scaled, mul_comm s]
    exact e.trans (taylor_err_mono n r h s hr hs)
  · simp only [eval_nil, sub_zero]; push_cast; exact Real.abs_cos_le_one _

theorem encl_sinScaled (n : ℕ) (r h : ℚ) :
    Encl r (fun s => Real.sin (s * h)) (sinScaledTM n r h) := by
  intro s hs
  unfold sinScaledTM
  split_ifs with hc
  · obtain ⟨hn, hr, hrh⟩ := hc
    have hx : |(h : ℝ) * s| ≤ 1 := by
      rw [abs_mul]
      calc |(h : ℝ)| * |s| ≤ |(h : ℝ)| * r := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ = ((r * |h| : ℚ) : ℝ) := by push_cast; ring
        _ ≤ 1 := by exact_mod_cast hrh
    have e := sin_expIPartial_error n ((h : ℝ) * s) hn hx
    rw [expIPartial_im_eq] at e
    simp only
    rw [eval_coefFrom_scaled, mul_comm s]
    exact e.trans (taylor_err_mono n r h s hr hs)
  · simp only [eval_nil, sub_zero]; push_cast; exact Real.abs_sin_le_one _

/-! ## Rational evaluation -/

def evalQ : Poly → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

theorem evalQ_cast : ∀ (p : Poly) (x : ℚ), ((evalQ p x : ℚ) : ℝ) = eval p x
  | [], _ => by simp [evalQ]
  | a :: p, x => by simp [evalQ, evalQ_cast p x]

/-! ## Enclosures of `(cos a, sin a)` -/

structure CS where
  c : ℚ
  s : ℚ
  e : ℚ

def CSEncl (x : ℝ) (A : CS) : Prop :=
  |Real.cos x - A.c| ≤ A.e ∧ |Real.sin x - A.s| ≤ A.e

def dbl (P : ℕ) (A : CS) : CS :=
  ⟨roundQ P (A.c ^ 2 - A.s ^ 2), roundQ P (2 * A.c * A.s), roundUpQ P (2 * A.e * (2 + A.e) + 1 / 2 ^ P)⟩

theorem dbl_encl (P : ℕ) (x : ℝ) (A : CS) (h : CSEncl x A) : CSEncl (2 * x) (dbl P A) := by
  obtain ⟨hc, hs⟩ := h
  have he : (0 : ℝ) ≤ A.e := (abs_nonneg _).trans hc
  have hC : |(A.c : ℝ)| ≤ 1 + A.e := by
    have := abs_sub_abs_le_abs_sub (A.c : ℝ) (Real.cos x)
    rw [abs_sub_comm] at this; linarith [Real.abs_cos_le_one x]
  have r1 := abs_sub_roundQ_le P (A.c ^ 2 - A.s ^ 2)
  have r2 := abs_sub_roundQ_le P (2 * A.c * A.s)
  have r1' : |((A.c ^ 2 - A.s ^ 2 : ℚ) : ℝ) - (roundQ P (A.c ^ 2 - A.s ^ 2) : ℝ)| ≤
      ((1 / 2 ^ P : ℚ) : ℝ) := by exact_mod_cast r1
  have r2' : |((2 * A.c * A.s : ℚ) : ℝ) - (roundQ P (2 * A.c * A.s) : ℝ)| ≤
      ((1 / 2 ^ P : ℚ) : ℝ) := by exact_mod_cast r2
  push_cast at r1' r2'
  have hS : |(A.s : ℝ)| ≤ 1 + A.e := by
    have := abs_sub_abs_le_abs_sub (A.s : ℝ) (Real.sin x)
    rw [abs_sub_comm] at this; linarith [Real.abs_sin_le_one x]
  have bc : |Real.cos x + A.c| ≤ 2 + A.e := by
    calc |Real.cos x + A.c| ≤ |Real.cos x| + |(A.c : ℝ)| := abs_add_le _ _
      _ ≤ 1 + (1 + A.e) := add_le_add (Real.abs_cos_le_one x) hC
      _ = 2 + A.e := by ring
  have bs : |Real.sin x + A.s| ≤ 2 + A.e := by
    calc |Real.sin x + A.s| ≤ |Real.sin x| + |(A.s : ℝ)| := abs_add_le _ _
      _ ≤ 1 + (1 + A.e) := add_le_add (Real.abs_sin_le_one x) hS
      _ = 2 + A.e := by ring
  have pc := mul_le_mul hc bc (abs_nonneg _) he
  have ps := mul_le_mul hs bs (abs_nonneg _) he
  have pcs := mul_le_mul hc (Real.abs_sin_le_one x) (abs_nonneg _) he
  have psc := mul_le_mul hs hC (abs_nonneg _) he
  rw [← abs_mul] at pc ps pcs psc
  have hup := le_roundUpQ P (2 * A.e * (2 + A.e) + 1 / 2 ^ P)
  have hup' : ((2 * A.e * (2 + A.e) + 1 / 2 ^ P : ℚ) : ℝ) ≤
      ((roundUpQ P (2 * A.e * (2 + A.e) + 1 / 2 ^ P) : ℚ) : ℝ) := by exact_mod_cast hup
  dsimp only [CSEncl, dbl]
  push_cast at hup' ⊢
  set R1 : ℝ := ((roundQ P (A.c ^ 2 - A.s ^ 2) : ℚ) : ℝ)
  set R2 : ℝ := ((roundQ P (2 * A.c * A.s) : ℚ) : ℝ)
  constructor
  · have hcos2 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
      rw [Real.cos_two_mul]; linarith [Real.cos_sq_add_sin_sq x]
    have e : Real.cos (2 * x) - R1 =
        ((Real.cos x - A.c) * (Real.cos x + A.c) - (Real.sin x - A.s) * (Real.sin x + A.s)) +
        (((A.c : ℝ) ^ 2 - (A.s : ℝ) ^ 2) - R1) := by rw [hcos2]; ring
    rw [e]
    have t1 := abs_add_le ((Real.cos x - A.c) * (Real.cos x + A.c) -
      (Real.sin x - A.s) * (Real.sin x + A.s)) (((A.c : ℝ) ^ 2 - (A.s : ℝ) ^ 2) - R1)
    have t2 := abs_sub ((Real.cos x - A.c) * (Real.cos x + A.c))
      ((Real.sin x - A.s) * (Real.sin x + A.s))
    linarith
  · have e : Real.sin (2 * x) - R2 =
        2 * ((Real.cos x - A.c) * Real.sin x) + 2 * ((Real.sin x - A.s) * A.c) +
          ((2 * A.c * A.s : ℝ) - R2) := by rw [Real.sin_two_mul]; ring
    rw [e]
    have t1 := abs_add_le (2 * ((Real.cos x - A.c) * Real.sin x) +
      2 * ((Real.sin x - A.s) * A.c)) ((2 * A.c * A.s : ℝ) - R2)
    have t2 := abs_add_le (2 * ((Real.cos x - A.c) * Real.sin x))
      (2 * ((Real.sin x - A.s) * A.c))
    have a1 : |2 * ((Real.cos x - A.c) * Real.sin x)| ≤ 2 * A.e := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    have a2 : |2 * ((Real.sin x - A.s) * A.c)| ≤ 2 * (A.e * (1 + A.e)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    nlinarith

def dblN (P : ℕ) : ℕ → CS → CS
  | 0, A => A
  | k + 1, A => dblN P k (dbl P A)

theorem dblN_encl (P : ℕ) : ∀ (k : ℕ) (x : ℝ) (A : CS), CSEncl x A →
    CSEncl (2 ^ k * x) (dblN P k A)
  | 0, x, A, h => by simpa [dblN] using h
  | k + 1, x, A, h => by
    have := dblN_encl P k (2 * x) (dbl P A) (dbl_encl P x A h)
    simp only [dblN]
    rw [pow_succ, mul_assoc]; exact this

/-- Base enclosure at `|x| ≤ 1`, rounded. -/
def baseCS (n P : ℕ) (x : ℚ) : CS :=
  let c := evalQ (coefFrom cosCoef 1 0 n) x
  let s := evalQ (coefFrom sinCoef 1 0 n) x
  ⟨roundQ P c, roundQ P s, roundUpQ P (taylorErr n |x| + 1 / 2 ^ P)⟩

theorem baseCS_encl (n P : ℕ) (x : ℚ) (hn : 0 < n) (hx : |x| ≤ 1) :
    CSEncl x (baseCS n P x) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have ec := cos_expIPartial_error n x hn hx'
  have es := sin_expIPartial_error n x hn hx'
  rw [expIPartial_re_eq, ← evalQ_cast] at ec
  rw [expIPartial_im_eq, ← evalQ_cast] at es
  have hte : |(x : ℝ)| ^ n * (((n.succ : ℕ) : ℝ) * (n.factorial * n : ℝ)⁻¹) =
      ((taylorErr n |x| : ℚ) : ℝ) := by rw [taylorErr_cast]; push_cast; ring
  rw [hte] at ec es
  have r1 := abs_sub_roundQ_le P (evalQ (coefFrom cosCoef 1 0 n) x)
  have r2 := abs_sub_roundQ_le P (evalQ (coefFrom sinCoef 1 0 n) x)
  have r1' : |((evalQ (coefFrom cosCoef 1 0 n) x : ℚ) : ℝ) -
      ((roundQ P (evalQ (coefFrom cosCoef 1 0 n) x) : ℚ) : ℝ)| ≤ ((1 / 2 ^ P : ℚ) : ℝ) := by
    exact_mod_cast r1
  have r2' : |((evalQ (coefFrom sinCoef 1 0 n) x : ℚ) : ℝ) -
      ((roundQ P (evalQ (coefFrom sinCoef 1 0 n) x) : ℚ) : ℝ)| ≤ ((1 / 2 ^ P : ℚ) : ℝ) := by
    exact_mod_cast r2
  have hup := le_roundUpQ P (taylorErr n |x| + 1 / 2 ^ P)
  have hup' : ((taylorErr n |x| + 1 / 2 ^ P : ℚ) : ℝ) ≤
      ((roundUpQ P (taylorErr n |x| + 1 / 2 ^ P) : ℚ) : ℝ) := by exact_mod_cast hup
  simp only [baseCS, CSEncl]
  push_cast at r1' r2' hup' ⊢
  constructor
  · calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ _ := add_le_add ec r1'
      _ ≤ _ := hup'
  · calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ _ := add_le_add es r2'
      _ ≤ _ := hup'

/-- Enclosure of `(cos a, sin a)` for any rational `a` (trivial if `|a| > 2^k`). -/
def cosSin (n k P : ℕ) (a : ℚ) : CS :=
  if 0 < n ∧ |a / 2 ^ k| ≤ 1 then dblN P k (baseCS n P (a / 2 ^ k)) else ⟨0, 0, 1⟩

theorem cosSin_encl (n k P : ℕ) (a : ℚ) : CSEncl a (cosSin n k P a) := by
  unfold cosSin
  split_ifs with h
  · have := dblN_encl P k _ _ (baseCS_encl n P (a / 2 ^ k) h.1 h.2)
    have e : (2 : ℝ) ^ k * ((a / 2 ^ k : ℚ) : ℝ) = a := by
      push_cast; field_simp
    rwa [e] at this
  · simp only [CSEncl]; push_cast
    simp only [sub_zero]
    exact ⟨Real.abs_cos_le_one _, Real.abs_sin_le_one _⟩

/-! ## Affine trigonometric Taylor models -/

structure TrigParams where
  n : ℕ      -- Taylor terms in the cell variable
  nb : ℕ     -- Taylor terms at the base angle
  k : ℕ      -- halvings
  P : ℕ      -- rounding bits

def cosAffTM (q : TrigParams) (r c h : ℚ) : TM :=
  let A := cosSin q.nb q.k q.P (c * h)
  TM.sub (TM.mul r (TM.ball A.c A.e) (cosScaledTM q.n r h))
    (TM.mul r (TM.ball A.s A.e) (sinScaledTM q.n r h))

def sinAffTM (q : TrigParams) (r c h : ℚ) : TM :=
  let A := cosSin q.nb q.k q.P (c * h)
  TM.add (TM.mul r (TM.ball A.s A.e) (cosScaledTM q.n r h))
    (TM.mul r (TM.ball A.c A.e) (sinScaledTM q.n r h))

theorem encl_cosAff (q : TrigParams) (r c h : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => Real.cos (((c : ℝ) + s) * h)) (cosAffTM q r c h) := by
  have A := cosSin_encl q.nb q.k q.P (c * h)
  have h1 := Encl.ball r _ _ _ A.1
  have h2 := Encl.ball r _ _ _ A.2
  have m1 := Encl.mul hr h1 (encl_cosScaled q.n r h)
  have m2 := Encl.mul hr h2 (encl_sinScaled q.n r h)
  have := Encl.sub m1 m2
  refine Encl.congr this ?_
  intro s _
  push_cast
  rw [show ((c : ℝ) + s) * h = c * h + s * h by ring, Real.cos_add]

theorem encl_sinAff (q : TrigParams) (r c h : ℚ) (hr : 0 ≤ r) :
    Encl r (fun s => Real.sin (((c : ℝ) + s) * h)) (sinAffTM q r c h) := by
  have A := cosSin_encl q.nb q.k q.P (c * h)
  have h1 := Encl.ball r _ _ _ A.2
  have h2 := Encl.ball r _ _ _ A.1
  have m1 := Encl.mul hr h1 (encl_cosScaled q.n r h)
  have m2 := Encl.mul hr h2 (encl_sinScaled q.n r h)
  have := Encl.add m1 m2
  refine Encl.congr this ?_
  intro s _
  push_cast
  rw [show ((c : ℝ) + s) * h = c * h + s * h by ring, Real.sin_add]

/-! ## Reciprocal and `sinc` -/

def invCoef (c : ℚ) (k : ℕ) : ℚ := (-1) ^ k / c ^ (k + 1)

/-- `1 / (c + s)` on `|s| ≤ r < c`. -/
def invTM (K : ℕ) (r c : ℚ) : TM :=
  ⟨coefFrom (invCoef c) 1 0 K, r ^ K / (c ^ K * (c - r))⟩

theorem inv_identity (c s : ℝ) (hc : c ≠ 0) (hcs : c + s ≠ 0) :
    ∀ K : ℕ, 1 / (c + s) - ∑ k ∈ Finset.range K, (-1) ^ k / c ^ (k + 1) * s ^ k =
      (-s) ^ K / (c ^ K * (c + s))
  | 0 => by simp
  | K + 1 => by
    rw [Finset.sum_range_succ, ← sub_sub, inv_identity c s hc hcs K]
    field_simp
    ring

theorem encl_inv (K : ℕ) (r c : ℚ) (hr : 0 ≤ r) (hrc : r < c) :
    Encl r (fun s => 1 / ((c : ℝ) + s)) (invTM K r c) := by
  intro s hs
  have hc : (0 : ℝ) < c := by exact_mod_cast (lt_of_le_of_lt hr hrc)
  have hcr : (0 : ℝ) < (c : ℝ) - r := by have : (r : ℝ) < c := by exact_mod_cast hrc
                                         linarith
  have hcs : (0 : ℝ) < c + s := by
    have := neg_abs_le s; linarith
  simp only [invTM]
  rw [eval_coefFrom_zero]
  have e := inv_identity (c : ℝ) s hc.ne' hcs.ne' K
  rw [show ∑ m ∈ Finset.range K, ((invCoef c m : ℚ) : ℝ) * (((1 : ℚ) : ℝ) * s) ^ m =
      ∑ k ∈ Finset.range K, (-1) ^ k / (c : ℝ) ^ (k + 1) * s ^ k by
    apply Finset.sum_congr rfl; intro m _; unfold invCoef; push_cast; ring, e]
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_of_pos hc, abs_of_pos hcs]
  apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hs K) (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := le_abs_self (-s); rw [abs_neg] at this; linarith

/-- `sinc ((c + s) / d)` on `|s| ≤ r`, for `0 ≤ r < c` and `0 < d`; trivial otherwise. -/
def sincAffTM (q : TrigParams) (K : ℕ) (r c d : ℚ) : TM :=
  if 0 ≤ r ∧ r < c ∧ 0 < d then
    TM.mul r (sinAffTM q r c (1 / d)) (TM.smul d (invTM K r c))
  else ⟨[], 1⟩

theorem encl_sincAff (q : TrigParams) (K : ℕ) (r c d : ℚ) :
    Encl r (fun s => Real.sinc (((c : ℝ) + s) / d)) (sincAffTM q K r c d) := by
  unfold sincAffTM
  split_ifs with h
  · obtain ⟨hr, hrc, hd⟩ := h
    have m := Encl.mul hr (encl_sinAff q r c (1 / d) hr) (Encl.smul d (encl_inv K r c hr hrc))
    refine Encl.congr m ?_
    intro s hs
    have hc : (0 : ℝ) < c := by exact_mod_cast (lt_of_le_of_lt hr hrc)
    have hcs : (0 : ℝ) < c + s := by
      have : (r : ℝ) < c := by exact_mod_cast hrc
      have := neg_abs_le s; linarith
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [Real.sinc_of_ne_zero (div_pos hcs hd').ne']
    push_cast
    field_simp
  · intro s _
    simp only [eval_nil, sub_zero]; push_cast
    exact Real.abs_sinc_le_one _

/-! ## Powers -/

def tmPow (r : ℚ) (P D : ℕ) (T : TM) : ℕ → TM
  | 0 => TM.const 1
  | m + 1 => TM.trim P D r (TM.mul r (tmPow r P D T m) T)

theorem encl_tmPow {r : ℚ} (hr : 0 ≤ r) (P D : ℕ) {f : ℝ → ℝ} {T : TM} (hf : Encl r f T) :
    ∀ m : ℕ, Encl r (fun s => f s ^ m) (tmPow r P D T m)
  | 0 => by
    have := Encl.const r 1
    refine Encl.congr this ?_; intro s _; simp
  | m + 1 => by
    have := Encl.trim hr (Encl.mul hr (encl_tmPow hr P D hf m) hf) P D
    refine Encl.congr this ?_; intro s _; ring

end AEGIS.RHKreinTrigTMV1
