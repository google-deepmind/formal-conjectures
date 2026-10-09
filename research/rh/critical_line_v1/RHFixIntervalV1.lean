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
# Fixed-point interval arithmetic (the `hardware_config.py` Q16.16 idea, made sound)

An interval is a pair of integers `(lo, hi)` read at scale `2^{-p}`: it encloses `x : ℝ` when
`lo / 2^p ≤ x ≤ hi / 2^p`.  Products are rounded outward (`fdiv` floors the lower end, `cdiv` ceils
the upper end), so every operation is sound: if the inputs enclose `x` and `y`, the output encloses
`x + y`, `-x`, `x * y`.  Everything is integer arithmetic, so the kernel evaluates it with `decide`.
AUTHORITY_EFFECT = NONE.
-/

namespace AEGIS.RHFixIntervalV1

/-- A fixed-point interval `[lo, hi] · 2^{-p}`. -/
structure Iv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

variable (p : ℕ)

/-- `I` encloses `x` at scale `2^{-p}`. -/
def Iv.Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) / 2 ^ p ≤ x ∧ x ≤ (I.hi : ℝ) / 2 ^ p

/-- Floor division by `2^p`. -/
def fdiv (m : ℤ) : ℤ := m / 2 ^ p

/-- Ceiling division by `2^p`. -/
def cdiv (m : ℤ) : ℤ := -((-m) / 2 ^ p)

lemma two_pow_pos : (0 : ℝ) < 2 ^ p := by positivity

lemma fdiv_le (m : ℤ) : ((fdiv p m : ℤ) : ℝ) ≤ (m : ℝ) / 2 ^ p := by
  rw [le_div_iff₀ (two_pow_pos p)]
  have h := Int.ediv_mul_le m (show (2 : ℤ) ^ p ≠ 0 by positivity)
  have : ((m / 2 ^ p * 2 ^ p : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  simpa [fdiv] using this

lemma le_cdiv (m : ℤ) : (m : ℝ) / 2 ^ p ≤ ((cdiv p m : ℤ) : ℝ) := by
  have h := fdiv_le p (-m)
  simp only [cdiv, Int.cast_neg]
  simp only [fdiv, Int.cast_neg] at h
  rw [neg_div] at h; linarith

def Iv.add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

def Iv.neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩

def Iv.mul (I J : Iv) : Iv :=
  ⟨fdiv p (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))),
   cdiv p (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))⟩

theorem Iv.mem_add {I J : Iv} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.add J).Mem p (x + y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [Iv.add, Int.cast_add, add_div] <;> linarith

theorem Iv.mem_neg {I : Iv} {x : ℝ} (hx : I.Mem p x) : I.neg.Mem p (-x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [Iv.neg, Int.cast_neg, neg_div] <;> linarith

/-- A product of two points of intervals lies between the extreme corner products. -/
lemma mul_between {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have lin : ∀ {u v w z : ℝ}, u ≤ w → w ≤ v →
      min (z * u) (z * v) ≤ z * w ∧ z * w ≤ max (z * u) (z * v) := by
    intro u v w z h1 h2
    rcases le_total 0 z with hz | hz
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left h1 hz),
        le_max_of_le_right (mul_le_mul_of_nonneg_left h2 hz)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left h2 hz),
        le_max_of_le_left (mul_le_mul_of_nonpos_left h1 hz)⟩
  obtain ⟨l1, u1⟩ := lin (z := x) hy1 hy2
  obtain ⟨lc, uc⟩ := lin (z := c) hx1 hx2
  obtain ⟨ld, ud⟩ := lin (z := d) hx1 hx2
  simp only [mul_comm c, mul_comm d] at lc uc ld ud
  constructor
  · refine le_trans ?_ l1
    rcases min_choice (x * c) (x * d) with h | h <;> rw [h]
    · exact le_trans (min_le_min (min_le_left _ _) (min_le_left _ _)) (by
        rcases min_choice (a * c) (b * c) with h' | h' <;> rw [h'] at lc <;>
          [exact le_trans (min_le_left _ _) lc; exact le_trans (min_le_right _ _) lc])
    · exact le_trans (min_le_min (min_le_right _ _) (min_le_right _ _)) (by
        rcases min_choice (a * d) (b * d) with h' | h' <;> rw [h'] at ld <;>
          [exact le_trans (min_le_left _ _) ld; exact le_trans (min_le_right _ _) ld])
  · refine le_trans u1 ?_
    rcases max_choice (x * c) (x * d) with h | h <;> rw [h]
    · exact le_trans (by
        rcases max_choice (a * c) (b * c) with h' | h' <;> rw [h'] at uc <;>
          [exact le_trans uc (le_max_left _ _); exact le_trans uc (le_max_right _ _)])
        (max_le_max (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (by
        rcases max_choice (a * d) (b * d) with h' | h' <;> rw [h'] at ud <;>
          [exact le_trans ud (le_max_left _ _); exact le_trans ud (le_max_right _ _)])
        (max_le_max (le_max_right _ _) (le_max_right _ _))

theorem Iv.mem_mul {I J : Iv} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.mul p J).Mem p (x * y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  obtain ⟨lo, hi⟩ := mul_between h1 h2 h3 h4
  have hp := two_pow_pos p
  have e : ∀ m n : ℤ, (m : ℝ) / 2 ^ p * ((n : ℝ) / 2 ^ p) = ((m * n : ℤ) : ℝ) / 2 ^ p / 2 ^ p := by
    intro m n; push_cast; field_simp
  simp only [e] at lo hi
  have cmin : ∀ a b c d : ℤ, min (min ((a : ℝ) / 2 ^ p / 2 ^ p) ((b : ℝ) / 2 ^ p / 2 ^ p))
      (min ((c : ℝ) / 2 ^ p / 2 ^ p) ((d : ℝ) / 2 ^ p / 2 ^ p)) =
      ((min (min a b) (min c d) : ℤ) : ℝ) / 2 ^ p / 2 ^ p := by
    intro a b c d
    have mono : Monotone (fun z : ℝ => z / 2 ^ p / 2 ^ p) := fun u v h => by
      simp only; gcongr
    simp only [Int.cast_min, ← mono.map_min]
  have cmax : ∀ a b c d : ℤ, max (max ((a : ℝ) / 2 ^ p / 2 ^ p) ((b : ℝ) / 2 ^ p / 2 ^ p))
      (max ((c : ℝ) / 2 ^ p / 2 ^ p) ((d : ℝ) / 2 ^ p / 2 ^ p)) =
      ((max (max a b) (max c d) : ℤ) : ℝ) / 2 ^ p / 2 ^ p := by
    intro a b c d
    have mono : Monotone (fun z : ℝ => z / 2 ^ p / 2 ^ p) := fun u v h => by
      simp only; gcongr
    simp only [Int.cast_max, ← mono.map_max]
  rw [cmin] at lo; rw [cmax] at hi
  constructor
  · refine le_trans ?_ lo
    exact div_le_div_of_nonneg_right (fdiv_le p _) hp.le
  · refine le_trans hi ?_
    exact div_le_div_of_nonneg_right (le_cdiv p _) hp.le

end AEGIS.RHFixIntervalV1

#print axioms AEGIS.RHFixIntervalV1.Iv.mem_mul
#print axioms AEGIS.RHFixIntervalV1.Iv.mem_add
