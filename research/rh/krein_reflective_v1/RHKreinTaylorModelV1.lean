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

import Mathlib

/-!
# Rational Taylor models

Polynomials are coefficient lists `a₀, a₁, …` over `ℚ`, evaluated by Horner's rule.
A Taylor model `(p, e)` encloses a real function `f` on `|s| ≤ r` when
`|f s - p(s)| ≤ e` there.  All operations are structurally recursive, so a closed
rational instance reduces in the kernel (`decide +kernel`); the lemmas below are the
one-time soundness proofs.

No RH statement is concluded.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHKreinTaylorModelV1

/-! ## Polynomials -/

abbrev Poly := List ℚ

/-- Horner evaluation at a real point. -/
def eval : Poly → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * eval p x

def padd : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def psmul (c : ℚ) : Poly → Poly
  | [] => []
  | a :: p => (c * a) :: psmul c p

def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (psmul a q) (0 :: pmul p q)

/-- `Σ |aₖ| rᵏ`, an upper bound for `|p(s)|` on `|s| ≤ r`. -/
def absBound : Poly → ℚ → ℚ
  | [], _ => 0
  | a :: p, r => |a| + r * absBound p r

/-- `a₀ - Σ_{k ≥ 1} |aₖ| rᵏ`, a lower bound for `p(s)` on `|s| ≤ r`. -/
def floorBound : Poly → ℚ → ℚ
  | [], _ => 0
  | a :: p, r => a - r * absBound p r

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (a : ℚ) (p : Poly) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := rfl

theorem eval_padd : ∀ (p q : Poly) (x : ℝ), eval (padd p q) x = eval p x + eval q x
  | [], q, x => by simp [padd]
  | a :: p, [], x => by simp [padd]
  | a :: p, b :: q, x => by
    simp only [padd, eval_cons, eval_padd p q x]; push_cast; ring

theorem eval_psmul (c : ℚ) : ∀ (p : Poly) (x : ℝ), eval (psmul c p) x = (c : ℝ) * eval p x
  | [], x => by simp [psmul]
  | a :: p, x => by
    simp only [psmul, eval_cons, eval_psmul c p x]; push_cast; ring

theorem eval_pmul : ∀ (p q : Poly) (x : ℝ), eval (pmul p q) x = eval p x * eval q x
  | [], q, x => by simp [pmul]
  | a :: p, q, x => by
    simp only [pmul, eval_padd, eval_psmul, eval_cons, eval_pmul p q x]; push_cast; ring

theorem absBound_nonneg (r : ℚ) (hr : 0 ≤ r) : ∀ p : Poly, 0 ≤ absBound p r
  | [] => le_refl 0
  | a :: p => by
    simp only [absBound]
    have := absBound_nonneg r hr p
    positivity

theorem abs_eval_le (r : ℚ) (hr : 0 ≤ r) (x : ℝ) (hx : |x| ≤ r) :
    ∀ p : Poly, |eval p x| ≤ (absBound p r : ℝ)
  | [] => by simp [absBound]
  | a :: p => by
    have ih := abs_eval_le r hr x hx p
    have hb : (0 : ℝ) ≤ absBound p r := by exact_mod_cast absBound_nonneg r hr p
    simp only [eval_cons, absBound]
    push_cast
    calc |(a : ℝ) + x * eval p x| ≤ |(a : ℝ)| + |x| * |eval p x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + (r : ℝ) * (absBound p r : ℝ) := by
          gcongr

theorem floorBound_le (r : ℚ) (hr : 0 ≤ r) (x : ℝ) (hx : |x| ≤ r) :
    ∀ p : Poly, (floorBound p r : ℝ) ≤ eval p x
  | [] => by simp [floorBound]
  | a :: p => by
    have h := abs_eval_le r hr x hx p
    have hb : (0 : ℝ) ≤ absBound p r := by exact_mod_cast absBound_nonneg r hr p
    simp only [eval_cons, floorBound]
    push_cast
    have h1 : |x * eval p x| ≤ (r : ℝ) * (absBound p r : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hx h (abs_nonneg _) ((abs_nonneg x).trans hx)
    linarith [neg_abs_le (x * eval p x)]

/-! ## Taylor models -/

/-- A Taylor model: polynomial and error radius. -/
structure TM where
  p : Poly
  e : ℚ

/-- `T` encloses `f` on `|s| ≤ r`. -/
def Encl (r : ℚ) (f : ℝ → ℝ) (T : TM) : Prop :=
  ∀ s : ℝ, |s| ≤ r → |f s - eval T.p s| ≤ T.e

def TM.const (a : ℚ) : TM := ⟨[a], 0⟩
def TM.var : TM := ⟨[0, 1], 0⟩
def TM.add (T U : TM) : TM := ⟨padd T.p U.p, T.e + U.e⟩
def TM.neg (T : TM) : TM := ⟨psmul (-1) T.p, T.e⟩
def TM.sub (T U : TM) : TM := TM.add T U.neg
def TM.smul (c : ℚ) (T : TM) : TM := ⟨psmul c T.p, |c| * T.e⟩
def TM.mul (r : ℚ) (T U : TM) : TM :=
  ⟨pmul T.p U.p, T.e * absBound U.p r + absBound T.p r * U.e + T.e * U.e⟩
/-- Constant with an error radius (an enclosed real number). -/
def TM.ball (a e : ℚ) : TM := ⟨[a], e⟩

theorem Encl.const (r : ℚ) (a : ℚ) : Encl r (fun _ => (a : ℝ)) (TM.const a) := by
  intro s _; simp [TM.const]

theorem Encl.var (r : ℚ) : Encl r (fun s => s) TM.var := by
  intro s _; simp [TM.var]

theorem Encl.ball (r : ℚ) (a e : ℚ) (y : ℝ) (h : |y - a| ≤ e) :
    Encl r (fun _ => y) (TM.ball a e) := by
  intro s _; simpa [TM.ball] using h

theorem Encl.add {r : ℚ} {f g : ℝ → ℝ} {T U : TM} (hf : Encl r f T) (hg : Encl r g U) :
    Encl r (fun s => f s + g s) (T.add U) := by
  intro s hs
  have h1 := hf s hs; have h2 := hg s hs
  simp only [TM.add, eval_padd]; push_cast
  calc |f s + g s - (eval T.p s + eval U.p s)| =
        |(f s - eval T.p s) + (g s - eval U.p s)| := by ring_nf
    _ ≤ |f s - eval T.p s| + |g s - eval U.p s| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem Encl.neg {r : ℚ} {f : ℝ → ℝ} {T : TM} (hf : Encl r f T) :
    Encl r (fun s => -f s) T.neg := by
  intro s hs
  have h1 := hf s hs
  simp only [TM.neg, eval_psmul]; push_cast
  calc |-f s - -1 * eval T.p s| = |f s - eval T.p s| := by
        rw [show -f s - -1 * eval T.p s = -(f s - eval T.p s) by ring, abs_neg]
    _ ≤ _ := h1

theorem Encl.sub {r : ℚ} {f g : ℝ → ℝ} {T U : TM} (hf : Encl r f T) (hg : Encl r g U) :
    Encl r (fun s => f s - g s) (T.sub U) := by
  have h := hf.add hg.neg
  intro s hs
  simpa [sub_eq_add_neg, TM.sub] using h s hs

theorem Encl.smul {r : ℚ} {f : ℝ → ℝ} {T : TM} (c : ℚ) (hf : Encl r f T) :
    Encl r (fun s => (c : ℝ) * f s) (T.smul c) := by
  intro s hs
  have h1 := hf s hs
  simp only [TM.smul, eval_psmul]; push_cast
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem Encl.mul {r : ℚ} (hr : 0 ≤ r) {f g : ℝ → ℝ} {T U : TM}
    (hf : Encl r f T) (hg : Encl r g U) :
    Encl r (fun s => f s * g s) (TM.mul r T U) := by
  intro s hs
  have h1 := hf s hs; have h2 := hg s hs
  have hT := abs_eval_le r hr s hs T.p
  have hU := abs_eval_le r hr s hs U.p
  simp only [TM.mul, eval_pmul]; push_cast
  set a := f s - eval T.p s
  set b := g s - eval U.p s
  have e : f s * g s - eval T.p s * eval U.p s =
      a * eval U.p s + eval T.p s * b + a * b := by
    simp only [a, b]; ring
  rw [e]
  have ha := abs_nonneg a; have hb := abs_nonneg b
  calc |a * eval U.p s + eval T.p s * b + a * b| ≤
        |a| * |eval U.p s| + |eval T.p s| * |b| + |a| * |b| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ (T.e : ℝ) * (absBound U.p r : ℝ) + (absBound T.p r : ℝ) * (U.e : ℝ) +
          (T.e : ℝ) * (U.e : ℝ) := by
        have hTe : (0 : ℝ) ≤ T.e := (abs_nonneg _).trans h1
        have hUe : (0 : ℝ) ≤ U.e := (abs_nonneg _).trans h2
        have hTb : (0 : ℝ) ≤ absBound T.p r := (abs_nonneg _).trans hT
        have hUb : (0 : ℝ) ≤ absBound U.p r := (abs_nonneg _).trans hU
        gcongr

theorem Encl.congr {r : ℚ} {f g : ℝ → ℝ} {T : TM} (hf : Encl r f T)
    (hfg : ∀ s : ℝ, |s| ≤ r → f s = g s) : Encl r g T := by
  intro s hs; rw [← hfg s hs]; exact hf s hs

theorem Encl.weaken {r : ℚ} {f : ℝ → ℝ} {T : TM} (hf : Encl r f T) (e' : ℚ) (he : T.e ≤ e') :
    Encl r f ⟨T.p, e'⟩ := by
  intro s hs; exact (hf s hs).trans (by exact_mod_cast he)

/-- The final sign: a Taylor model whose floor exceeds its error encloses a nonnegative
function. -/
theorem Encl.nonneg {r : ℚ} (hr : 0 ≤ r) {f : ℝ → ℝ} {T : TM} (hf : Encl r f T)
    (hpos : T.e ≤ floorBound T.p r) : ∀ s : ℝ, |s| ≤ r → 0 ≤ f s := by
  intro s hs
  have h1 := hf s hs
  have h2 := floorBound_le r hr s hs T.p
  have h3 : (T.e : ℝ) ≤ floorBound T.p r := by exact_mod_cast hpos
  linarith [neg_abs_le (f s - eval T.p s)]

/-! ## Rounding and truncation -/

/-- Round to the dyadic grid `2^-k` (toward `-∞`). -/
def roundQ (k : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k

theorem abs_sub_roundQ_le (k : ℕ) (q : ℚ) : |q - roundQ k q| ≤ 1 / 2 ^ k := by
  unfold roundQ
  have hpos : (0 : ℚ) < 2 ^ k := by positivity
  have h1 := Int.floor_le (q * 2 ^ k)
  have h2 := Int.lt_floor_add_one (q * 2 ^ k)
  have e : q - (⌊q * 2 ^ k⌋ : ℚ) / 2 ^ k = (q * 2 ^ k - ⌊q * 2 ^ k⌋) / 2 ^ k := by
    field_simp
  rw [e, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos, abs_le]
  constructor <;> linarith

def roundPoly (k : ℕ) (p : Poly) : Poly := p.map (roundQ k)

/-- Round up to the dyadic grid `2^-k`. -/
def roundUpQ (k : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ k⌉ : ℚ) / 2 ^ k

theorem le_roundUpQ (k : ℕ) (q : ℚ) : q ≤ roundUpQ k q := by
  unfold roundUpQ
  have hpos : (0 : ℚ) < 2 ^ k := by positivity
  rw [le_div_iff₀ hpos]
  exact Int.le_ceil _

/-- Keep the first `n` coefficients and round them; the rest goes into the error. -/
def TM.trim (k n : ℕ) (r : ℚ) (T : TM) : TM :=
  let q := roundPoly k (T.p.take n)
  ⟨q, roundUpQ k (T.e + absBound (padd T.p (psmul (-1) q)) r)⟩

theorem Encl.trim {r : ℚ} (hr : 0 ≤ r) {f : ℝ → ℝ} {T : TM} (hf : Encl r f T) (k n : ℕ) :
    Encl r f (TM.trim k n r T) := by
  intro s hs
  have h1 := hf s hs
  set q := roundPoly k (T.p.take n)
  have h2 := abs_eval_le r hr s hs (padd T.p (psmul (-1) q))
  rw [eval_padd, eval_psmul] at h2
  simp only [TM.trim]
  have hup := le_roundUpQ k (T.e + absBound (padd T.p (psmul (-1) q)) r)
  have hup' : ((T.e + absBound (padd T.p (psmul (-1) q)) r : ℚ) : ℝ) ≤
      ((roundUpQ k (T.e + absBound (padd T.p (psmul (-1) q)) r) : ℚ) : ℝ) := by
    exact_mod_cast hup
  push_cast at h2 hup' ⊢
  calc |f s - eval q s| = |(f s - eval T.p s) + (eval T.p s + -1 * eval q s)| := by ring_nf
    _ ≤ |f s - eval T.p s| + |eval T.p s + -1 * eval q s| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ ≤ _ := hup'

end AEGIS.RHKreinTaylorModelV1
