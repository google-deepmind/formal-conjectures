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

import RHKreinHatFastV1
import RHKreinL105DataV1
import AEGISOverlay.RHKreinDigammaLowerBoundV1

/-!
# Taylor-model components for the `L = 21/20` certificate

* `col_encl2`: a hat column on a wide cell, with `Complex.exp_bound'` (`|x| ≤ (n+1)/2`) in place of
  the `|x| ≤ 1` bound;
* `hatAccL`: the column sum over a coefficient list with phases advanced by one rotation each;
* `hatBallTM`: the crude bound `|(2/50) sinc² Σ| ≤ (2/50)(100/t)² Σ|c|`;
* `sincZeroTM`: `sinc` on a cell centred at `0`;
* `headTM`: `Σ_{n<K₀} quarterTerm` through the complex geometric series of `1/(z₀ + i s/2)`;
* `shiftPoly`: re-centring a polynomial.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinL105TMV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinRotTMV1
open AEGIS.RHKreinHatFastV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open AEGIS.RHKreinDigammaLowerBoundV1
open Complex

/-! ## Wide hat columns -/

theorem expIPartial_error2 (n : ℕ) (x : ℝ) (hx : |x| ≤ ((n : ℝ) + 1) / 2) :
    ‖Complex.exp ((x : ℂ) * I) - expIPartial n x‖ ≤ 2 * |x| ^ n / n.factorial := by
  have hxc : ‖((x : ℂ) * I)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      div_le_iff₀ (by positivity)]
    push_cast; linarith
  have h := Complex.exp_bound' hxc
  calc ‖Complex.exp ((x : ℂ) * I) - expIPartial n x‖ ≤ ‖(x : ℂ) * I‖ ^ n / n.factorial * 2 := h
    _ = 2 * |x| ^ n / n.factorial := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; ring

/-- Error of one wide column. -/
def colErr2 (n : ℕ) (r h : ℚ) (A : CS) : ℚ :=
  A.e + (1 + A.e) * (2 * (r * |h|) ^ n / n.factorial)

theorem col_encl2 (n : ℕ) (r c h : ℚ) (hr : 0 ≤ r) (hrh : r * |h| ≤ ((n : ℚ) + 1) / 2) (A : CS)
    (hA : ZEncl ((c * h : ℚ) : ℝ) A) (s : ℝ) (hs : |s| ≤ r) :
    |Real.cos (((c : ℝ) + s) * h) - eval (phaseRow A.c A.s h 0 n 1) s| ≤ colErr2 n r h A := by
  rw [eval_phaseRow_zero]
  have hsh : |s * (h : ℝ)| ≤ ((r * |h| : ℚ) : ℝ) := by
    rw [abs_mul]; push_cast
    exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hx : |s * (h : ℝ)| ≤ ((n : ℝ) + 1) / 2 := by
    refine hsh.trans ?_
    have : ((r * |h| : ℚ) : ℝ) ≤ (((n : ℚ) + 1) / 2 : ℚ) := by exact_mod_cast hrh
    simpa using this
  have hE := expIPartial_error2 n (s * h) hx
  have hT : 2 * |s * (h : ℝ)| ^ n / n.factorial ≤ ((2 * (r * |h|) ^ n / n.factorial : ℚ) : ℝ) := by
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (abs_nonneg _)
    simpa using hsh
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
  unfold colErr2
  push_cast
  apply add_le_add hA
  have hT' : 2 * |s * (h : ℝ)| ^ n / n.factorial ≤ 2 * ((r : ℝ) * |(h : ℝ)|) ^ n / n.factorial := by
    simpa using hT
  exact mul_le_mul hnZ (hE.trans hT') (norm_nonneg _) (by linarith)

/-! ## The hat sum over a coefficient list -/

/-- `Σ_k a_k cos (t (h + k/50))`. -/
def hatSumL : List ℚ → ℚ → ℝ → ℝ
  | [], _, _ => 0
  | a :: l, h, t => (a : ℝ) * Real.cos (t * h) + hatSumL l (h + 1 / 50) t

def absSum : List ℚ → ℚ
  | [] => 0
  | a :: l => |a| + absSum l

theorem absSum_nonneg : ∀ l : List ℚ, 0 ≤ absSum l
  | [] => le_refl _
  | a :: l => by simp only [absSum]; have := absSum_nonneg l; positivity

theorem abs_hatSumL_le : ∀ (l : List ℚ) (h : ℚ) (t : ℝ), |hatSumL l h t| ≤ absSum l
  | [], _, _ => by simp [hatSumL, absSum]
  | a :: l, h, t => by
    simp only [hatSumL, absSum]; push_cast
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_hatSumL_le l _ t))
    rw [abs_mul]
    calc |(a : ℝ)| * |Real.cos (t * h)| ≤ |(a : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |(a : ℝ)| := mul_one _

/-- Accumulated hat polynomial and error; the phase is advanced by `B ≈ exp(i c/50)`. -/
def hatAccL (n P : ℕ) (r : ℚ) (B : CS) : List ℚ → ℚ → CS → Poly → ℚ → Poly × ℚ
  | [], _, _, p, e => (p, e)
  | a :: l, h, A, p, e =>
    if r * |h| ≤ ((n : ℚ) + 1) / 2 then
      hatAccL n P r B l (h + 1 / 50) (rotC P A B) (padd p (psmul a (phaseRow A.c A.s h 0 n 1)))
        (e + |a| * colErr2 n r h A)
    else hatAccL n P r B l (h + 1 / 50) (rotC P A B) p (e + |a|)

theorem hatAccL_spec (n P : ℕ) (r c : ℚ) (hr : 0 ≤ r) (B : CS)
    (hB : ZEncl ((c / 50 : ℚ) : ℝ) B) :
    ∀ (l : List ℚ) (h : ℚ) (A : CS) (p : Poly) (e : ℚ) (f : ℝ → ℝ),
      ZEncl ((c * h : ℚ) : ℝ) A → Encl r f ⟨p, e⟩ →
      Encl r (fun s => f s + hatSumL l h ((c : ℝ) + s))
        ⟨(hatAccL n P r B l h A p e).1, (hatAccL n P r B l h A p e).2⟩
  | [], h, A, p, e, f, _, hf => by
    intro s hs; simpa [hatAccL, hatSumL] using hf s hs
  | a :: l, h, A, p, e, f, hA, hf => by
    have hrot : ZEncl ((c * (h + 1 / 50) : ℚ) : ℝ) (rotC P A B) := by
      have := rotC_encl P hA hB
      have e2 : ((c * h : ℚ) : ℝ) + ((c / 50 : ℚ) : ℝ) = ((c * (h + 1 / 50) : ℚ) : ℝ) := by
        push_cast; ring
      rwa [e2] at this
    simp only [hatAccL]
    split_ifs with hc
    · have hcol : Encl r (fun s => (a : ℝ) * Real.cos (((c : ℝ) + s) * h))
          ⟨psmul a (phaseRow A.c A.s h 0 n 1), |a| * colErr2 n r h A⟩ := by
        intro s hs
        simp only [eval_psmul]
        rw [← mul_sub, abs_mul]; push_cast
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast col_encl2 n r c h hr hc A hA s hs)
          (abs_nonneg _)
      have hsum : Encl r (fun s => f s + (a : ℝ) * Real.cos (((c : ℝ) + s) * h))
          ⟨padd p (psmul a (phaseRow A.c A.s h 0 n 1)), e + |a| * colErr2 n r h A⟩ :=
        Encl.add hf hcol
      have := hatAccL_spec n P r c hr B hB l (h + 1 / 50) (rotC P A B) _ _ _ hrot hsum
      refine Encl.congr this ?_
      intro s _; simp only [hatSumL]; ring
    · have hcol : Encl r (fun s => (a : ℝ) * Real.cos (((c : ℝ) + s) * h)) ⟨[], |a|⟩ := by
        intro s _
        simp only [eval_nil, sub_zero, abs_mul]; push_cast
        calc |(a : ℝ)| * |Real.cos (((c : ℝ) + s) * h)| ≤ |(a : ℝ)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ = |(a : ℝ)| := mul_one _
      have hsum : Encl r (fun s => f s + (a : ℝ) * Real.cos (((c : ℝ) + s) * h)) ⟨p, e + |a|⟩ := by
        have := Encl.add hf hcol
        have hp : padd p [] = p := by cases p <;> rfl
        simpa [TM.add, hp] using this
      have := hatAccL_spec n P r c hr B hB l (h + 1 / 50) (rotC P A B) _ _ _ hrot hsum
      refine Encl.congr this ?_
      intro s _; simp only [hatSumL]; ring

/-! ## Crude hat bound -/

theorem sinc_sq_le_inv (x : ℝ) (hx : 0 < x) : Real.sinc x ^ 2 ≤ 1 / x ^ 2 := by
  rw [Real.sinc_of_ne_zero hx.ne', div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _

theorem sinc_sq_le_one (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sinc_le_one _

def hatBallTM (S r c : ℚ) : TM :=
  if 0 < c - r then TM.ball 0 (2 / 50 * (100 / (c - r)) ^ 2 * S) else TM.ball 0 (2 / 50 * S)

theorem encl_hatBall (l : List ℚ) (h r c : ℚ) :
    Encl r (fun s => 2 / 50 * Real.sinc (((c : ℝ) + s) / 100) ^ 2 * hatSumL l h ((c : ℝ) + s))
      (hatBallTM (absSum l) r c) := by
  intro s hs
  have hS := abs_hatSumL_le l h ((c : ℝ) + s)
  have hS0 : (0 : ℝ) ≤ absSum l := by exact_mod_cast absSum_nonneg l
  unfold hatBallTM
  split_ifs with hcr
  · simp only [TM.ball, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_zero, sub_zero]
    have hcr' : (0 : ℝ) < (c : ℝ) - r := by exact_mod_cast hcr
    have hts : (c : ℝ) - r ≤ (c : ℝ) + s := by have := neg_abs_le s; linarith
    have hpos : 0 < ((c : ℝ) + s) / 100 := div_pos (by linarith) (by norm_num)
    have hsinc := sinc_sq_le_inv _ hpos
    have hinv : 1 / (((c : ℝ) + s) / 100) ^ 2 ≤ (100 / ((c : ℝ) - r)) ^ 2 := by
      rw [one_div, ← inv_pow, inv_div]
      apply pow_le_pow_left₀ (div_pos (by norm_num) (by linarith)).le
      exact div_le_div_of_nonneg_left (by norm_num) hcr' hts
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / 50),
      abs_of_nonneg (sq_nonneg _)]
    push_cast
    calc 2 / 50 * Real.sinc (((c : ℝ) + s) / 100) ^ 2 * |hatSumL l h ((c : ℝ) + s)| ≤
        2 / 50 * (100 / ((c : ℝ) - r)) ^ 2 * absSum l := by
          apply mul_le_mul _ hS (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (hsinc.trans hinv) (by norm_num)
      _ = _ := by ring
  · simp only [TM.ball, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_zero, sub_zero]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / 50),
      abs_of_nonneg (sq_nonneg _)]
    push_cast
    calc 2 / 50 * Real.sinc (((c : ℝ) + s) / 100) ^ 2 * |hatSumL l h ((c : ℝ) + s)| ≤
        2 / 50 * 1 * absSum l := by
          apply mul_le_mul _ hS (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (sinc_sq_le_one _) (by norm_num)
      _ = _ := by ring

/-! ## `sinc` at centre `0` -/

def sincZeroTM (n : ℕ) (r d : ℚ) : TM :=
  if 1 < n ∧ 0 ≤ r ∧ 0 < d ∧ r ≤ d then
    ⟨coefFrom (fun j => sinCoef (j + 1)) (1 / d) 0 (n - 1),
      (r / d) ^ (n - 1) * ((n + 1 : ℚ) / (n.factorial * n))⟩
  else ⟨[], 1⟩

theorem sinCoef_zero : sinCoef 0 = 0 := by simp [sinCoef]

theorem encl_sincZero (n : ℕ) (r d : ℚ) :
    Encl r (fun s => Real.sinc (s / d)) (sincZeroTM n r d) := by
  intro s hs
  unfold sincZeroTM
  split_ifs with hc
  · obtain ⟨hn, hr, hd, hrd⟩ := hc
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    set x : ℝ := s / d with hxdef
    have hxr : |x| ≤ ((r / d : ℚ) : ℝ) := by
      rw [hxdef, abs_div, abs_of_pos hd']; push_cast
      exact div_le_div_of_nonneg_right hs hd'.le
    have hrd' : ((r / d : ℚ) : ℝ) ≤ 1 := by
      have : r / d ≤ 1 := (div_le_one hd).mpr hrd
      exact_mod_cast this
    have hx1 : |x| ≤ 1 := hxr.trans hrd'
    have hn0 : 0 < n := by omega
    have e := sin_expIPartial_error n x hn0 hx1
    rw [expIPartial_im_eq, eval_coefFrom_zero] at e
    -- Σ_{m<n} sinCoef m x^m = x · Σ_{j<n-1} sinCoef (j+1) x^j
    have hsplit : (∑ m ∈ Finset.range n, (sinCoef m : ℝ) * ((1 : ℚ) * x) ^ m) =
        x * ∑ j ∈ Finset.range (n - 1), (sinCoef (j + 1) : ℝ) * x ^ j := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [Nat.add_sub_cancel, sinCoef_zero, Rat.cast_zero, zero_mul, add_zero, Rat.cast_one,
        one_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    have hpoly : eval (coefFrom (fun j => sinCoef (j + 1)) (1 / d) 0 (n - 1)) s =
        ∑ j ∈ Finset.range (n - 1), (sinCoef (j + 1) : ℝ) * x ^ j := by
      rw [eval_coefFrom_zero]
      apply Finset.sum_congr rfl; intro j _
      rw [hxdef]; push_cast; ring
    simp only
    rw [hpoly]
    rw [hsplit] at e
    by_cases hx0 : x = 0
    · have hsinc : Real.sinc (s / d) = 1 := by rw [← hxdef, hx0, Real.sinc_zero]
      rw [hsinc]
      have hsum : (∑ j ∈ Finset.range (n - 1), (sinCoef (j + 1) : ℝ) * x ^ j) = 1 := by
        rw [hx0]
        obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
        rw [hk, Finset.sum_range_succ']
        simp [sinCoef]
      rw [hsum, sub_self, abs_zero]
      push_cast; positivity
    · rw [← hxdef, Real.sinc_of_ne_zero hx0]
      have hxpos : 0 < |x| := abs_pos.mpr hx0
      have key : Real.sin x / x - ∑ j ∈ Finset.range (n - 1), (sinCoef (j + 1) : ℝ) * x ^ j =
          (Real.sin x - x * ∑ j ∈ Finset.range (n - 1), (sinCoef (j + 1) : ℝ) * x ^ j) / x := by
        field_simp
      rw [key, abs_div]
      rw [div_le_iff₀ hxpos]
      refine e.trans ?_
      have hpow : |x| ^ n = |x| ^ (n - 1) * |x| := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow]
      push_cast
      have hC : (0 : ℝ) ≤ ((n : ℝ) + 1) * ((n.factorial : ℝ) * n)⁻¹ := by positivity
      have hpw : |x| ^ (n - 1) ≤ ((r : ℝ) / d) ^ (n - 1) := by
        apply pow_le_pow_left₀ (abs_nonneg _); simpa using hxr
      have key := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hC) (abs_nonneg x)
      calc _ = |x| ^ (n - 1) * (((n : ℝ) + 1) * ((n.factorial : ℝ) * n)⁻¹) * |x| := by ring
        _ ≤ ((r : ℝ) / d) ^ (n - 1) * (((n : ℝ) + 1) * ((n.factorial : ℝ) * n)⁻¹) * |x| := key
        _ = _ := by ring
  · simp only [eval_nil, sub_zero]; push_cast
    exact Real.abs_sinc_le_one _

/-! ## Digamma head through a complex geometric series -/

def headCoef (rr ri : ℚ) : ℕ → ℚ → ℚ → Poly
  | 0, _, _ => []
  | m + 1, br, bi => br :: headCoef rr ri m (br * rr - bi * ri) (br * ri + bi * rr)

theorem eval_headCoef (rr ri : ℚ) (s : ℝ) :
    ∀ (m : ℕ) (br bi : ℚ), eval (headCoef rr ri m br bi) s =
      (∑ k ∈ Finset.range m, ((br : ℂ) + (bi : ℂ) * I) * ((rr : ℂ) + (ri : ℂ) * I) ^ k *
        ((s : ℂ) ^ k)).re
  | 0, _, _ => by simp [headCoef]
  | m + 1, br, bi => by
    simp only [headCoef, eval_cons]
    rw [eval_headCoef rr ri s m]
    have hβ : (((br * rr - bi * ri : ℚ) : ℂ) + ((br * ri + bi * rr : ℚ) : ℂ) * I) =
        ((br : ℂ) + (bi : ℂ) * I) * ((rr : ℂ) + (ri : ℂ) * I) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [hβ, Finset.sum_range_succ']
    have hsum : (∑ k ∈ Finset.range m, ((br : ℂ) + (bi : ℂ) * I) * ((rr : ℂ) + (ri : ℂ) * I) ^ (k + 1) *
          (s : ℂ) ^ (k + 1)) = (s : ℂ) * ∑ k ∈ Finset.range m, ((br : ℂ) + (bi : ℂ) * I) *
          ((rr : ℂ) + (ri : ℂ) * I) * ((rr : ℂ) + (ri : ℂ) * I) ^ k * (s : ℂ) ^ k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [hsum, Complex.add_re, Complex.re_ofReal_mul]
    simp only [pow_zero, mul_one, Complex.add_re, Complex.ratCast_re, Complex.mul_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul]
    ring

/-- `max a (|c|/2)`, a lower bound for `|a + i c/2|`. -/
def zetaLB (a c : ℚ) : ℚ := max a (|c| / 2)

def headTerm (D : ℕ) (r c : ℚ) (n : ℕ) : TM :=
  let a : ℚ := (n : ℚ) + 1 / 4
  let m2 : ℚ := a ^ 2 + c ^ 2 / 4
  let z := zetaLB a c
  if r / 2 < z then
    ⟨padd [1 / ((n : ℚ) + 1)]
        (psmul (-1) (headCoef (-(c / 4) / m2) (-(a / 2) / m2) D (a / m2) (-(c / 2) / m2))),
      (r / 2) ^ D / (z ^ D * (z - r / 2))⟩
  else ⟨[], 1 / ((n : ℚ) + 1) + 1 / a⟩

theorem norm_ge_zetaLB (a c : ℚ) (ha : 0 < a) :
    ((zetaLB a c : ℚ) : ℝ) ≤ ‖(a : ℂ) + ((c / 2 : ℚ) : ℂ) * I‖ := by
  unfold zetaLB
  push_cast
  apply max_le
  · have h := Complex.abs_re_le_norm ((a : ℂ) + ((c : ℂ) / 2) * I)
    simp at h
    rwa [abs_of_pos (by exact_mod_cast ha)] at h
  · have h := Complex.abs_im_le_norm ((a : ℂ) + ((c : ℂ) / 2) * I)
    simp at h
    rw [abs_div] at h; simpa using h

theorem encl_headTerm (D : ℕ) (r c : ℚ) (hr : 0 ≤ r) (n : ℕ) :
    Encl r (fun s => quarterTerm ((c : ℝ) + s) n) (headTerm D r c n) := by
  intro s hs
  set a : ℚ := (n : ℚ) + 1 / 4 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hq : quarterTerm ((c : ℝ) + s) n =
      1 / ((n : ℝ) + 1) - (a : ℝ) / ((a : ℝ) ^ 2 + ((c : ℝ) + s) ^ 2 / 4) := by
    simp only [quarterTerm, hadef]; push_cast; ring
  unfold headTerm
  simp only []
  split_ifs with hz
  · set m2 : ℚ := a ^ 2 + c ^ 2 / 4 with hm2
    have hm2pos : 0 < m2 := by rw [hm2]; positivity
    set z0 : ℂ := (a : ℂ) + ((c / 2 : ℚ) : ℂ) * I with hz0
    set w : ℂ := ((s / 2 : ℝ) : ℂ) * I with hw
    have hz0ne : z0 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [hz0] at this; linarith
    have hnz := norm_ge_zetaLB a c ha
    rw [← hz0] at hnz
    have hzpos : (0 : ℝ) < ((zetaLB a c : ℚ) : ℝ) - r / 2 := by
      have : ((r / 2 : ℚ) : ℝ) < ((zetaLB a c : ℚ) : ℝ) := by exact_mod_cast hz
      push_cast at this; linarith
    have hwn : ‖w‖ = |s| / 2 := by
      rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]
      norm_num
    have hwr : ‖w‖ ≤ r / 2 := by rw [hwn]; linarith
    have hzw : ((zetaLB a c : ℚ) : ℝ) - r / 2 ≤ ‖z0 + w‖ := by
      have := norm_sub_norm_le z0 (-w)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    have hzwne : z0 + w ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hzw; linarith
    -- real part identity
    have hre : (1 / (z0 + w)).re = (a : ℝ) / ((a : ℝ) ^ 2 + ((c : ℝ) + s) ^ 2 / 4) := by
      have hre1 : (z0 + w).re = a := by simp [hz0, hw]
      have hre2 : (z0 + w).im = ((c : ℝ) + s) / 2 := by simp [hz0, hw]; ring
      rw [one_div, Complex.inv_re, Complex.normSq_apply, hre1, hre2]
      congr 1; ring
    -- coefficient identity
    have hcoef : ∀ k : ℕ, (((a / m2 : ℚ) : ℂ) + ((-(c / 2) / m2 : ℚ) : ℂ) * I) *
        (((-(c / 4) / m2 : ℚ) : ℂ) + ((-(a / 2) / m2 : ℚ) : ℂ) * I) ^ k * (s : ℂ) ^ k =
        (-w) ^ k / z0 ^ (k + 1) := by
      have hm2r : (m2 : ℝ) = (a : ℝ) ^ 2 + (c : ℝ) ^ 2 / 4 := by rw [hm2]; push_cast; ring
      have hm2r0 : (m2 : ℝ) ≠ 0 := by exact_mod_cast hm2pos.ne'
      have hb : (((a / m2 : ℚ) : ℂ) + ((-(c / 2) / m2 : ℚ) : ℂ) * I) * z0 = 1 := by
        apply Complex.ext <;> simp [hz0] <;> field_simp <;> rw [hm2r] <;> ring
      have hr' : (((-(c / 4) / m2 : ℚ) : ℂ) + ((-(a / 2) / m2 : ℚ) : ℂ) * I) * z0 = -I / 2 := by
        apply Complex.ext <;> simp [hz0] <;> field_simp <;> rw [hm2r] <;> ring
      have hb' : ((a / m2 : ℚ) : ℂ) + ((-(c / 2) / m2 : ℚ) : ℂ) * I = 1 / z0 := by
        rw [eq_div_iff hz0ne]; exact hb
      have hr'' : ((-(c / 4) / m2 : ℚ) : ℂ) + ((-(a / 2) / m2 : ℚ) : ℂ) * I = (-I / 2) / z0 := by
        rw [eq_div_iff hz0ne]; exact hr'
      intro k
      rw [hb', hr'', hw, div_pow, pow_succ]
      push_cast
      field_simp
      ring
    have hident : 1 / (z0 + w) - ∑ k ∈ Finset.range D, (-w) ^ k / z0 ^ (k + 1) =
        (-w) ^ D / (z0 ^ D * (z0 + w)) := by
      have key : ∀ K : ℕ, 1 / (z0 + w) - ∑ k ∈ Finset.range K, (-w) ^ k / z0 ^ (k + 1) =
          (-w) ^ K / (z0 ^ K * (z0 + w)) := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, ← sub_sub, ih]
          field_simp
          ring
      exact key D
    have hpoly : eval (headCoef (-(c / 4) / m2) (-(a / 2) / m2) D (a / m2) (-(c / 2) / m2)) s =
        (∑ k ∈ Finset.range D, (-w) ^ k / z0 ^ (k + 1)).re := by
      rw [eval_headCoef]; congr 1
      apply Finset.sum_congr rfl; intro k _; exact hcoef k
    simp only [eval_padd, eval_psmul, eval_cons, eval_nil, mul_zero, add_zero]
    rw [hpoly, hq, ← hre]
    push_cast
    have e1 : 1 / ((n : ℝ) + 1) - (1 / (z0 + w)).re -
        (1 / ((n : ℝ) + 1) + -1 * (∑ k ∈ Finset.range D, (-w) ^ k / z0 ^ (k + 1)).re) =
        -(1 / (z0 + w) - ∑ k ∈ Finset.range D, (-w) ^ k / z0 ^ (k + 1)).re := by
      rw [Complex.sub_re]; ring
    rw [e1, abs_neg, hident]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg]
    have hz0p : 0 < ‖z0‖ := norm_pos_iff.mpr hz0ne
    have hzl : (0 : ℝ) < ((zetaLB a c : ℚ) : ℝ) := by linarith [(by positivity : (0 : ℝ) ≤ r / 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖w‖ ^ D * (((zetaLB a c : ℚ) : ℝ) ^ D * (((zetaLB a c : ℚ) : ℝ) - r / 2)) ≤
        (r / 2) ^ D * (‖z0‖ ^ D * ‖z0 + w‖) := by
          apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwr _) _ (by positivity)
            (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ hzl.le hnz _) hzw hzpos.le (by positivity)
      _ = _ := by ring
  · simp only [eval_nil, sub_zero]
    rw [hq]
    have hT : 0 < (a : ℝ) ^ 2 + ((c : ℝ) + s) ^ 2 / 4 := by positivity
    have h1 : (a : ℝ) / ((a : ℝ) ^ 2 + ((c : ℝ) + s) ^ 2 / 4) ≤ 1 / (a : ℝ) := by
      rw [div_le_div_iff₀ hT ha']; nlinarith [sq_nonneg ((c : ℝ) + s)]
    have h2 : 0 ≤ (a : ℝ) / ((a : ℝ) ^ 2 + ((c : ℝ) + s) ^ 2 / 4) := by positivity
    have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hacast : (a : ℝ) = (n : ℝ) + 1 / 4 := by rw [hadef]; push_cast; ring
    rw [abs_le]; push_cast; rw [← hacast]; constructor <;> linarith

def headTM (K0 D : ℕ) (r c : ℚ) : ℕ → TM
  | 0 => ⟨[], 0⟩
  | m + 1 => if m < K0 then TM.add (headTM K0 D r c m) (headTerm D r c m) else headTM K0 D r c m

theorem encl_headTM (K0 D : ℕ) (r c : ℚ) (hr : 0 ≤ r) :
    ∀ m : ℕ, m ≤ K0 → Encl r (fun s => ∑ n ∈ Finset.range m, quarterTerm ((c : ℝ) + s) n)
      (headTM K0 D r c m)
  | 0, _ => by intro s _; simp [headTM]
  | m + 1, hm => by
    have ih := encl_headTM K0 D r c hr m (by omega)
    simp only [headTM, show m < K0 by omega, if_true]
    refine Encl.congr (Encl.add ih (encl_headTerm D r c hr m)) ?_
    intro s _; rw [Finset.sum_range_succ]

/-! ## Re-centring -/

/-- `(X + h) · q`. -/
def mulXh (h : ℚ) (q : Poly) : Poly := padd (psmul h q) (0 :: q)

theorem eval_mulXh (h : ℚ) (q : Poly) (s : ℝ) : eval (mulXh h q) s = ((h : ℝ) + s) * eval q s := by
  simp only [mulXh, eval_padd, eval_psmul, eval_cons]; push_cast; ring

def shiftPoly (h : ℚ) : Poly → Poly
  | [] => []
  | a :: p => padd [a] (mulXh h (shiftPoly h p))

theorem eval_shiftPoly (h : ℚ) (s : ℝ) : ∀ p : Poly, eval (shiftPoly h p) s = eval p ((h : ℝ) + s)
  | [] => by simp [shiftPoly]
  | a :: p => by
    simp only [shiftPoly, eval_padd, eval_mulXh, eval_cons, eval_nil, eval_shiftPoly h s p]
    ring

end AEGIS.RHKreinL105TMV1

#print axioms AEGIS.RHKreinL105TMV1.hatAccL_spec
#print axioms AEGIS.RHKreinL105TMV1.encl_headTM
#print axioms AEGIS.RHKreinL105TMV1.encl_sincZero
#print axioms AEGIS.RHKreinL105TMV1.encl_hatBall
