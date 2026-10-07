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

import RHKreinTrigTMV1

/-!
# Complex-norm phase enclosures and rotations

`ZEncl x A : ‖exp (x i) - (A.c + A.s i)‖ ≤ A.e`.  A product of two enclosed phases is enclosed
with the additive error `eA + (1 + eA) eB` plus rounding, so an arithmetic progression of angles
costs one rotation per step.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinRotTMV1

open AEGIS.RHKreinTaylorModelV1
open AEGIS.RHKreinTrigTMV1
open AEGIS.RHKreinFiniteIntervalKernelV1
open Complex

def zOf (A : CS) : ℂ := (A.c : ℂ) + (A.s : ℂ) * I

def ZEncl (x : ℝ) (A : CS) : Prop := ‖Complex.exp ((x : ℂ) * I) - zOf A‖ ≤ A.e

theorem ZEncl.toCS {x : ℝ} {A : CS} (h : ZEncl x A) : CSEncl x A := by
  have hre := Complex.abs_re_le_norm (Complex.exp ((x : ℂ) * I) - zOf A)
  have him := Complex.abs_im_le_norm (Complex.exp ((x : ℂ) * I) - zOf A)
  simp only [zOf, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hre him
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, Complex.ratCast_re,
    Complex.ratCast_im] at hre him
  exact ⟨hre.trans h, him.trans h⟩

theorem norm_zOf_le {x : ℝ} {A : CS} (h : ZEncl x A) : ‖zOf A‖ ≤ 1 + A.e := by
  have h1 : ‖Complex.exp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
  have := norm_sub_norm_le (zOf A) (Complex.exp ((x : ℂ) * I))
  rw [norm_sub_rev] at this
  unfold ZEncl at h
  linarith

theorem norm_round_le (P : ℕ) (a b : ℚ) :
    ‖((a : ℂ) + (b : ℂ) * I) - (((roundQ P a : ℚ) : ℂ) + ((roundQ P b : ℚ) : ℂ) * I)‖ ≤
      2 / 2 ^ P := by
  have ha := abs_sub_roundQ_le P a
  have hb := abs_sub_roundQ_le P b
  have ha' : |((a - roundQ P a : ℚ) : ℝ)| ≤ ((1 / 2 ^ P : ℚ) : ℝ) := by exact_mod_cast ha
  have hb' : |((b - roundQ P b : ℚ) : ℝ)| ≤ ((1 / 2 ^ P : ℚ) : ℝ) := by exact_mod_cast hb
  push_cast at ha' hb'
  have e : ((a : ℂ) + (b : ℂ) * I) - (((roundQ P a : ℚ) : ℂ) + ((roundQ P b : ℚ) : ℂ) * I) =
      (((a : ℝ) - (roundQ P a : ℝ) : ℝ) : ℂ) + (((b : ℝ) - (roundQ P b : ℝ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero]
  have h2 : (2 : ℝ) / 2 ^ P = 1 / 2 ^ P + 1 / 2 ^ P := by ring
  rw [h2]
  exact add_le_add ha' hb'

/-- Rotation: the product of two enclosed phases. -/
def rotC (P : ℕ) (A B : CS) : CS :=
  ⟨roundQ P (A.c * B.c - A.s * B.s), roundQ P (A.c * B.s + A.s * B.c),
    roundUpQ P (A.e + (1 + A.e) * B.e + 2 / 2 ^ P)⟩

theorem rotC_encl (P : ℕ) {x y : ℝ} {A B : CS} (hA : ZEncl x A) (hB : ZEncl y B) :
    ZEncl (x + y) (rotC P A B) := by
  have hnA := norm_zOf_le hA
  have hb1 : ‖Complex.exp ((y : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y
  have hup := le_roundUpQ P (A.e + (1 + A.e) * B.e + 2 / 2 ^ P)
  have hup' : ((A.e + (1 + A.e) * B.e + 2 / 2 ^ P : ℚ) : ℝ) ≤
      ((roundUpQ P (A.e + (1 + A.e) * B.e + 2 / 2 ^ P) : ℚ) : ℝ) := by exact_mod_cast hup
  push_cast at hup'
  have hprod : zOf A * zOf B =
      (((A.c * B.c - A.s * B.s : ℚ) : ℂ) + ((A.c * B.s + A.s * B.c : ℚ) : ℂ) * I) := by
    unfold zOf; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hround := norm_round_le P (A.c * B.c - A.s * B.s) (A.c * B.s + A.s * B.c)
  unfold ZEncl
  have hexp : Complex.exp (((x + y : ℝ) : ℂ) * I) =
      Complex.exp ((x : ℂ) * I) * Complex.exp ((y : ℂ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [hexp]
  set a := Complex.exp ((x : ℂ) * I)
  set b := Complex.exp ((y : ℂ) * I)
  have e : a * b - zOf (rotC P A B) =
      (a - zOf A) * b + zOf A * (b - zOf B) + (zOf A * zOf B - zOf (rotC P A B)) := by ring
  rw [e]
  have t1 : ‖(a - zOf A) * b‖ ≤ A.e := by rw [norm_mul, hb1, mul_one]; exact hA
  have t2 : ‖zOf A * (b - zOf B)‖ ≤ (1 + A.e) * B.e := by
    rw [norm_mul]; exact mul_le_mul hnA hB (norm_nonneg _) (by linarith [norm_nonneg (zOf A)])
  have t3 : ‖zOf A * zOf B - zOf (rotC P A B)‖ ≤ 2 / 2 ^ P := by
    rw [hprod]; unfold rotC zOf; exact hround
  calc ‖(a - zOf A) * b + zOf A * (b - zOf B) + (zOf A * zOf B - zOf (rotC P A B))‖ ≤
      ‖(a - zOf A) * b‖ + ‖zOf A * (b - zOf B)‖ + ‖zOf A * zOf B - zOf (rotC P A B)‖ :=
        norm_add₃_le
    _ ≤ A.e + (1 + A.e) * B.e + 2 / 2 ^ P := by linarith
    _ ≤ _ := by simp only [rotC]; exact hup'

/-- Base phase at `|x| ≤ 1`. -/
def baseZ (n P : ℕ) (x : ℚ) : CS :=
  ⟨roundQ P (evalQ (coefFrom cosCoef 1 0 n) x), roundQ P (evalQ (coefFrom sinCoef 1 0 n) x),
    roundUpQ P (taylorErr n |x| + 2 / 2 ^ P)⟩

theorem baseZ_encl (n P : ℕ) (x : ℚ) (hn : 0 < n) (hx : |x| ≤ 1) : ZEncl x (baseZ n P x) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have he := expIPartial_error n x hn hx'
  have hz : expIPartial n x = ((evalQ (coefFrom cosCoef 1 0 n) x : ℚ) : ℂ) +
      ((evalQ (coefFrom sinCoef 1 0 n) x : ℚ) : ℂ) * I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ratCast_re,
        Complex.ratCast_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [expIPartial_re_eq, ← evalQ_cast]
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
        Complex.ratCast_im, mul_zero, mul_one, zero_add]
      rw [expIPartial_im_eq, ← evalQ_cast]
      simp
  have hte : |(x : ℝ)| ^ n * (((n.succ : ℕ) : ℝ) * (n.factorial * n : ℝ)⁻¹) =
      ((taylorErr n |x| : ℚ) : ℝ) := by rw [taylorErr_cast]; push_cast; ring
  rw [hte, hz] at he
  have hround := norm_round_le P (evalQ (coefFrom cosCoef 1 0 n) x)
    (evalQ (coefFrom sinCoef 1 0 n) x)
  have hup := le_roundUpQ P (taylorErr n |x| + 2 / 2 ^ P)
  have hup' : ((taylorErr n |x| + 2 / 2 ^ P : ℚ) : ℝ) ≤
      ((roundUpQ P (taylorErr n |x| + 2 / 2 ^ P) : ℚ) : ℝ) := by exact_mod_cast hup
  push_cast at hup'
  unfold ZEncl
  calc ‖Complex.exp ((x : ℂ) * I) - zOf (baseZ n P x)‖ ≤
      ‖Complex.exp ((x : ℂ) * I) - (((evalQ (coefFrom cosCoef 1 0 n) x : ℚ) : ℂ) +
        ((evalQ (coefFrom sinCoef 1 0 n) x : ℚ) : ℂ) * I)‖ +
      ‖(((evalQ (coefFrom cosCoef 1 0 n) x : ℚ) : ℂ) +
        ((evalQ (coefFrom sinCoef 1 0 n) x : ℚ) : ℂ) * I) - zOf (baseZ n P x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (taylorErr n |x| : ℝ) + 2 / 2 ^ P := by
        apply add_le_add he; unfold zOf baseZ; exact hround
    _ ≤ _ := by simp only [baseZ]; exact hup'

def dblZ (P : ℕ) : ℕ → CS → CS
  | 0, A => A
  | k + 1, A => dblZ P k (rotC P A A)

theorem dblZ_encl (P : ℕ) : ∀ (k : ℕ) (x : ℝ) (A : CS), ZEncl x A → ZEncl (2 ^ k * x) (dblZ P k A)
  | 0, x, A, h => by simpa [dblZ] using h
  | k + 1, x, A, h => by
    have h2 : ZEncl (x + x) (rotC P A A) := rotC_encl P h h
    have := dblZ_encl P k (x + x) (rotC P A A) h2
    simp only [dblZ]
    rw [pow_succ, mul_assoc, two_mul]; exact this

/-- Phase enclosure for any rational angle (trivial if `|a| > 2^k`). -/
def phaseZ (n k P : ℕ) (a : ℚ) : CS :=
  if 0 < n ∧ |a / 2 ^ k| ≤ 1 then dblZ P k (baseZ n P (a / 2 ^ k)) else ⟨0, 0, 1⟩

theorem phaseZ_encl (n k P : ℕ) (a : ℚ) : ZEncl a (phaseZ n k P a) := by
  unfold phaseZ
  split_ifs with h
  · have := dblZ_encl P k _ _ (baseZ_encl n P (a / 2 ^ k) h.1 h.2)
    have e : (2 : ℝ) ^ k * ((a / 2 ^ k : ℚ) : ℝ) = a := by push_cast; field_simp
    rwa [e] at this
  · unfold ZEncl
    rw [show zOf ⟨0, 0, 1⟩ = 0 by simp [zOf], sub_zero, Complex.norm_exp_ofReal_mul_I]
    norm_num

/-! ## Affine models from a given phase -/

def cosFromTM (n : ℕ) (r h : ℚ) (A : CS) : TM :=
  TM.sub (TM.mul r (TM.ball A.c A.e) (cosScaledTM n r h))
    (TM.mul r (TM.ball A.s A.e) (sinScaledTM n r h))

theorem encl_cosFrom (n : ℕ) (r c h : ℚ) (hr : 0 ≤ r) (A : CS) (hA : ZEncl ((c * h : ℚ) : ℝ) A) :
    Encl r (fun s => Real.cos (((c : ℝ) + s) * h)) (cosFromTM n r h A) := by
  have hA' := hA.toCS
  have m1 := Encl.mul hr (Encl.ball r _ _ _ hA'.1) (encl_cosScaled n r h)
  have m2 := Encl.mul hr (Encl.ball r _ _ _ hA'.2) (encl_sinScaled n r h)
  refine Encl.congr (Encl.sub m1 m2) ?_
  intro s _
  push_cast
  rw [show ((c : ℝ) + s) * h = c * h + s * h by ring, Real.cos_add]

end AEGIS.RHKreinRotTMV1
