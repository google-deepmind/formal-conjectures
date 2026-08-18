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

import FormalConjecturesUtil

/-!
# $a(n) = 16n^2 + 1$

*References:*
- [A108211](https://oeis.org/A108211)
-/

namespace OeisA108211

/--
The primary defining sequence `a`.
`a n` is defined as $16n^2 + 1$.
-/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 17 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 65 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 145 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 257 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 401 := by decide

open Real

/-
### Auxiliary development for `conjecture`

The strategy is to sandwich `T n := log 2 - (H_{2n} - H_n)` (the tail of the paired
alternating harmonic series) between an explicit telescoping certificate `hf n` and
`hf n + gf n`, and then to show that the whole window `[hf n, hf n + gf n]` sits strictly
inside `(1/(4n) - 1/(16n²+1), 1/(4n) - 1/(16n²+2))`, which pins the floor to `16n² + 1`.
All polynomial inequalities are certified via a shift `x = 1 + t`, `t ≥ 0`, making every
coefficient in the resulting polynomial nonnegative, so `linarith` closes them from
nonnegativity of powers of `t`.
-/

section A108211Aux

open Finset Filter
open scoped Topology

set_option maxHeartbeats 2000000

noncomputable section

/- #### The certificate functions -/

/-- Numerator of the telescoping certificate. -/
private def Apoly (x : ℝ) : ℝ :=
  1024 * x ^ 5 + 5888 * x ^ 4 + 12928 * x ^ 3 + 13312 * x ^ 2 + 6148 * x + 843

/-- Telescoping certificate `h`. -/
private def hf (x : ℝ) : ℝ :=
  Apoly x / (4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7))

/-- Majorant certificate `g`. -/
private def gf (x : ℝ) : ℝ := 60 / (4 * x + 1) ^ 7

/-- The summand, as a function of a real variable. -/
private def ff (x : ℝ) : ℝ := 1 / ((2 * x + 1) * (2 * x + 2))

/-- The summand, as a function of a natural number. -/
private def ffun (m : ℕ) : ℝ := 1 / ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2))

/- #### Polynomial certificates -/

/-- Certificate C3 : `h - f₁ > 0`. -/
@[category API, AMS 11]
private lemma cert5 (x : ℝ) (hx : 1 ≤ x) :
    (16 * x ^ 2 - 4 * x + 1) *
        (4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7))
      < Apoly x * (4 * x * (16 * x ^ 2 + 1)) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5]

/-- Certificate C4 : `f₂ - h - g > 0`. -/
@[category API, AMS 11]
private lemma cert6 (x : ℝ) (hx : 1 ≤ x) :
    (Apoly x * (4 * x + 1) ^ 6 +
        240 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) *
        (4 * x * (8 * x ^ 2 + 1))
      < (8 * x ^ 2 - 2 * x + 1) *
        (4 * (4 * x + 1) ^ 7 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]

/-- Certificate C2 : `Δ(x) + g(x+1) ≤ g(x)`, cleared of denominators. -/
@[category API, AMS 11]
private lemma cert2 (x : ℝ) (hx : 1 ≤ x) :
    (126 * (16 * x ^ 2 + 120 * x + 119) * (4 * x + 5) ^ 7 +
        4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) * 60) * (4 * x + 1) ^ 7
      ≤ 60 * (4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) * (4 * x + 5) ^ 7) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6, pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9, pow_nonneg ht 10,
    pow_nonneg ht 11, pow_nonneg ht 12, pow_nonneg ht 13, pow_nonneg ht 14, pow_nonneg ht 15,
    pow_nonneg ht 16]

/-- Decay certificate : `x * A(x) ≤ denominator`, i.e. `hf x ≤ 1/x`. -/
@[category API, AMS 11]
private lemma cert7 (x : ℝ) (hx : 1 ≤ x) :
    x * Apoly x
      ≤ 4 * (4 * x + 1) * (2 * x + 1) * (4 * x + 3) * (4 * x + 5) * (2 * x + 3) * (4 * x + 7) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = 1 + t := ⟨x - 1, by linarith, by ring⟩
  simp only [Apoly]
  linarith [ht, pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6]

/- #### The defect identity -/

/-- `Δ(x) = ff x - (hf x - hf (x+1))` in closed form. -/
@[category API, AMS 11]
private lemma delta_eq (x : ℝ) (hx : 0 ≤ x) :
    ff x - (hf x - hf (x + 1))
      = 126 * (16 * x ^ 2 + 120 * x + 119) /
        (4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
          ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
          ((4 * x + 9) * (2 * x + 5) * (4 * x + 11))) := by
  have h1 : (4 * x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h2 : (2 * x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h3 : (4 * x + 3 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h4 : (4 * x + 5 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h5 : (2 * x + 3 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h6 : (4 * x + 7 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h7 : (4 * x + 9 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h8 : (2 * x + 5 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h9 : (4 * x + 11 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h10 : (x + 1 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h11 : (2 * x + 2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  simp only [ff, hf, Apoly]
  field_simp
  ring

@[category API, AMS 11]
private lemma delta_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ ff x - (hf x - hf (x + 1)) := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have h7 : (0:ℝ) < 4 * x + 9 := by linarith
  have h8 : (0:ℝ) < 2 * x + 5 := by linarith
  have h9 : (0:ℝ) < 4 * x + 11 := by linarith
  have h10 : (0:ℝ) < x + 1 := by linarith
  rw [delta_eq x hx]
  positivity

@[category API, AMS 11]
private lemma delta_le (x : ℝ) (hx : 1 ≤ x) :
    ff x - (hf x - hf (x + 1)) ≤ gf x - gf (x + 1) := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have h7 : (0:ℝ) < 4 * x + 9 := by linarith
  have h8 : (0:ℝ) < 2 * x + 5 := by linarith
  have h9 : (0:ℝ) < 4 * x + 11 := by linarith
  have h10 : (0:ℝ) < x + 1 := by linarith
  have hDd : (0:ℝ) < 4 * (x + 1) * ((4 * x + 1) * (2 * x + 1) * (4 * x + 3)) *
      ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)) *
      ((4 * x + 9) * (2 * x + 5) * (4 * x + 11)) := by positivity
  have he : (4:ℝ) * (x + 1) + 1 = 4 * x + 5 := by ring
  rw [delta_eq x hx0]
  simp only [gf, he]
  rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt hDd) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [cert2 x hx]

/- #### Elementary bounds on `hf` and `gf` -/

@[category API, AMS 11]
private lemma hf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ hf x := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  simp only [hf, Apoly]
  positivity

@[category API, AMS 11]
private lemma gf_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ gf x := by
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  simp only [gf]
  positivity

@[category API, AMS 11]
private lemma hf_le_inv (x : ℝ) (hx : 1 ≤ x) : hf x ≤ 1 / x := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  simp only [hf]
  rw [div_le_div_iff₀ (by positivity) hx0]
  linarith [cert7 x hx]

/- #### The window inequalities -/

@[category API, AMS 11]
private lemma window_low (x : ℝ) (hx : 1 ≤ x) : (4 * x)⁻¹ - (16 * x ^ 2 + 1)⁻¹ < hf x := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have hq : (0:ℝ) < 16 * x ^ 2 + 1 := by positivity
  have e : (4 * x)⁻¹ - (16 * x ^ 2 + 1)⁻¹
      = (16 * x ^ 2 - 4 * x + 1) / (4 * x * (16 * x ^ 2 + 1)) := by
    field_simp
    ring
  rw [e]
  simp only [hf]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith [cert5 x hx]

@[category API, AMS 11]
private lemma window_high (x : ℝ) (hx : 1 ≤ x) :
    hf x + gf x < (4 * x)⁻¹ - (16 * x ^ 2 + 2)⁻¹ := by
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < 4 * x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  have h3 : (0:ℝ) < 4 * x + 3 := by linarith
  have h4 : (0:ℝ) < 4 * x + 5 := by linarith
  have h5 : (0:ℝ) < 2 * x + 3 := by linarith
  have h6 : (0:ℝ) < 4 * x + 7 := by linarith
  have e2 : (4 * x)⁻¹ - (16 * x ^ 2 + 2)⁻¹
      = (8 * x ^ 2 - 2 * x + 1) / (4 * x * (8 * x ^ 2 + 1)) := by
    field_simp
    ring
  have e3 : hf x + gf x
      = (Apoly x * (4 * x + 1) ^ 6 +
          240 * ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) /
        (4 * (4 * x + 1) ^ 7 *
          ((2 * x + 1) * (4 * x + 3) * ((4 * x + 5) * (2 * x + 3) * (4 * x + 7)))) := by
    simp only [hf, gf]
    field_simp
    ring
  rw [e2, e3, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith [cert6 x hx]

/- #### The harmonic partial sums and `log 2` -/

/-- `Hh N = H_N`, the `N`-th harmonic number. -/
private def Hh (N : ℕ) : ℝ := ∑ i ∈ range N, ((i : ℝ) + 1)⁻¹

@[category API, AMS 11]
private lemma Hh_succ (N : ℕ) : Hh (N + 1) = Hh N + ((N : ℝ) + 1)⁻¹ := by
  simp only [Hh, Finset.sum_range_succ]

@[category API, AMS 11]
private lemma Hh_diff (n : ℕ) : Hh (2 * n) - Hh n = ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
  have h : n ≤ 2 * n := by omega
  simp only [Hh]
  rw [← Finset.sum_Ico_eq_sub _ h, Finset.sum_Ico_eq_sum_range]
  rw [show 2 * n - n = n by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

@[category API, AMS 11]
private lemma ffun_nonneg (m : ℕ) : 0 ≤ ffun m := by
  simp only [ffun]
  positivity

@[category API, AMS 11]
private lemma sum_ffun (n : ℕ) : ∑ m ∈ range n, ffun m = Hh (2 * n) - Hh n := by
  induction n with
  | zero => simp [Hh]
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [Finset.sum_range_succ, ih, e]
    simp only [Hh, Finset.sum_range_succ, ffun]
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

@[category API, AMS 11]
private lemma harm_upper (n : ℕ) (hn : 1 ≤ n) : Hh (2 * n) - Hh n ≤ Real.log 2 := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : ((n : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  rw [Hh_diff]
  set g : ℕ → ℝ := fun j => Real.log ((n : ℝ) + (j : ℝ)) with hg
  have key : ∀ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ ≤ g (i + 1) - g i := by
    intro i _
    have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have ha : (1:ℝ) ≤ (n : ℝ) + (i : ℝ) := by linarith
    have hb : (0:ℝ) < (n : ℝ) + (i : ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < ((n : ℝ) + (i : ℝ)) / ((n : ℝ) + (i : ℝ) + 1) :=
      div_pos (by linarith) hb
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have e : ((n : ℝ) + (i : ℝ)) / ((n : ℝ) + (i : ℝ) + 1) - 1 = -(((n : ℝ) + (i : ℝ) + 1)⁻¹) := by
      field_simp
      ring
    rw [e] at hlog
    have hgi : g (i + 1) = Real.log ((n : ℝ) + (i : ℝ) + 1) := by
      simp only [hg]
      congr 1
      push_cast
      ring
    rw [hgi]
    simp only [hg]
    linarith
  calc ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹
      ≤ ∑ i ∈ range n, (g (i + 1) - g i) := Finset.sum_le_sum key
    _ = g n - g 0 := Finset.sum_range_sub g n
    _ = Real.log 2 := by
        simp only [hg, Nat.cast_zero, add_zero]
        rw [show (n : ℝ) + (n : ℝ) = 2 * (n : ℝ) by ring, Real.log_mul two_ne_zero hn0]
        ring

@[category API, AMS 11]
private lemma harm_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1) ≤ Hh (2 * n) - Hh n := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Hh_diff]
  set g : ℕ → ℝ := fun j => Real.log ((n : ℝ) + (j : ℝ) + 1) with hg
  have key : ∀ i ∈ range n, g (i + 1) - g i ≤ ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
    intro i _
    have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hb : (0:ℝ) < (n : ℝ) + (i : ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < ((n : ℝ) + (i : ℝ) + 2) / ((n : ℝ) + (i : ℝ) + 1) :=
      div_pos (by linarith) hb
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have e : ((n : ℝ) + (i : ℝ) + 2) / ((n : ℝ) + (i : ℝ) + 1) - 1 = ((n : ℝ) + (i : ℝ) + 1)⁻¹ := by
      field_simp
      ring
    rw [e] at hlog
    have hgi : g (i + 1) = Real.log ((n : ℝ) + (i : ℝ) + 2) := by
      simp only [hg]
      congr 1
      push_cast
      ring
    rw [hgi]
    simp only [hg]
    linarith
  calc Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)
      = g n - g 0 := by
        simp only [hg, Nat.cast_zero, add_zero]
        rw [show (n : ℝ) + (n : ℝ) + 1 = 2 * (n : ℝ) + 1 by ring]
    _ = ∑ i ∈ range n, (g (i + 1) - g i) := (Finset.sum_range_sub g n).symm
    _ ≤ ∑ i ∈ range n, ((n : ℝ) + (i : ℝ) + 1)⁻¹ := Finset.sum_le_sum key

@[category API, AMS 11]
private lemma tendsto_lower :
    Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 (Real.log 2)) := by
  have h1 : ∀ n : ℕ, Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)
      = Real.log ((2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.log_div (by positivity) (by positivity)]
  have h2 : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 2) := by
    have he : ∀ n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) = 2 - 1 / ((n : ℝ) + 1) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [tendsto_congr he]
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.sub this
  simp_rw [h1]
  exact h2.log two_ne_zero

@[category API, AMS 11]
private lemma tendsto_partial :
    Tendsto (fun n : ℕ => Hh (2 * n) - Hh n) atTop (𝓝 (Real.log 2)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_lower tendsto_const_nhds
    (eventually_atTop.2 ⟨1, fun n hn => harm_lower n hn⟩)
    (eventually_atTop.2 ⟨1, fun n hn => harm_upper n hn⟩)

@[category API, AMS 11]
private lemma summable_ffun : Summable ffun := by
  refine summable_of_sum_range_le (c := Real.log 2) ffun_nonneg fun n => ?_
  rw [sum_ffun]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Hh, Nat.mul_zero, sub_self]
    exact Real.log_nonneg (by norm_num)
  · exact harm_upper n hn

@[category API, AMS 11]
private lemma hasSum_ffun : HasSum ffun (Real.log 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg ffun_nonneg]
  simpa only [sum_ffun] using tendsto_partial

/- #### The tail `T` -/

/-- The tail of the paired alternating harmonic series. -/
private def T (n : ℕ) : ℝ := ∑' m : ℕ, ffun (m + n)

@[category API, AMS 11]
private lemma T_eq (n : ℕ) : Real.log 2 - (Hh (2 * n) - Hh n) = T n := by
  have h := summable_ffun.sum_add_tsum_nat_add n
  rw [hasSum_ffun.tsum_eq, sum_ffun] at h
  simp only [T]
  linarith

@[category API, AMS 11]
private lemma Icc_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹ = Hh (2 * n) - Hh n := by
  have e : Finset.Icc (n + 1) (2 * n) = Finset.Ico (n + 1) (2 * n + 1) := by
    ext k
    simp
  rw [e, Finset.sum_Ico_eq_sum_range, Hh_diff, show 2 * n + 1 - (n + 1) = n by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/- #### The sandwich -/

@[category API, AMS 11]
private lemma T_bounds (n : ℕ) (hn : 1 ≤ n) :
    hf (n : ℝ) ≤ T n ∧ T n ≤ hf (n : ℝ) + gf (n : ℝ) := by
  have hx1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxm : ∀ m : ℕ, (1:ℝ) ≤ (n : ℝ) + (m : ℝ) := by
    intro m
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  set F : ℕ → ℝ := fun m => hf ((n : ℝ) + (m : ℝ)) with hF
  set G : ℕ → ℝ := fun m => gf ((n : ℝ) + (m : ℝ)) with hG
  have hFs : ∀ m : ℕ, F (m + 1) = hf ((n : ℝ) + (m : ℝ) + 1) := by
    intro m
    simp only [hF]
    congr 1
    push_cast
    ring
  have hGs : ∀ m : ℕ, G (m + 1) = gf ((n : ℝ) + (m : ℝ) + 1) := by
    intro m
    simp only [hG]
    congr 1
    push_cast
    ring
  have hffe : ∀ m : ℕ, ffun (m + n) = ff ((n : ℝ) + (m : ℝ)) := by
    intro m
    simp only [ffun, ff]
    push_cast
    ring_nf
  have hsum : Summable (fun m : ℕ => ffun (m + n)) := (summable_nat_add_iff n).2 summable_ffun
  have hP : Tendsto (fun N : ℕ => ∑ m ∈ range N, ffun (m + n)) atTop (𝓝 (T n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hF0 : F 0 = hf (n : ℝ) := by simp [hF]
  have hG0 : G 0 = gf (n : ℝ) := by simp [hG]
  -- lower estimate on partial sums
  have hlow : ∀ N : ℕ, F 0 - F N ≤ ∑ m ∈ range N, ffun (m + n) := by
    intro N
    rw [← Finset.sum_range_sub' F N]
    refine Finset.sum_le_sum fun m _ => ?_
    have := delta_nonneg ((n : ℝ) + (m : ℝ)) (by linarith [hxm m])
    rw [hFs m, hffe m]
    linarith
  -- upper estimate on partial sums
  have hup : ∀ N : ℕ, ∑ m ∈ range N, ffun (m + n) ≤ (F 0 - F N) + (G 0 - G N) := by
    intro N
    rw [← Finset.sum_range_sub' F N, ← Finset.sum_range_sub' G N, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ => ?_
    have := delta_le ((n : ℝ) + (m : ℝ)) (hxm m)
    rw [hFs m, hGs m, hffe m]
    linarith
  -- `F N → 0`
  have hFtend : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero (f := F) (g := fun N : ℕ => 1 / ((N : ℝ) + 1))
      (fun N => hf_nonneg _ (by linarith [hxm N])) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : hf ((n : ℝ) + (N : ℝ)) ≤ 1 / ((n : ℝ) + (N : ℝ)) := hf_le_inv _ (hxm N)
    have h2 : (1:ℝ) / ((n : ℝ) + (N : ℝ)) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    simp only [hF]
    linarith
  constructor
  · have hA : Tendsto (fun N : ℕ => F 0 - F N) atTop (𝓝 (F 0 - 0)) :=
      tendsto_const_nhds.sub hFtend
    rw [sub_zero] at hA
    rw [← hF0]
    exact le_of_tendsto_of_tendsto' hA hP hlow
  · rw [← hF0, ← hG0]
    refine le_of_tendsto' hP fun N => ?_
    have h1 : 0 ≤ F N := hf_nonneg _ (by linarith [hxm N])
    have h2 : 0 ≤ G N := gf_nonneg _ (by linarith [hxm N])
    linarith [hup N]

end

end A108211Aux

/--
Conjecture:
$$a(n) = \left\lfloor \frac{1}{\frac{1}{4n} - \log(2) +
  \frac{1}{n+1} + \frac{1}{n+2} + \dots + \frac{1}{2n}} \right\rfloor.$$
-/
@[category research solved, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 0) :
    (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ) := by
  have hn1 : 1 ≤ n := hn
  have hx1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : (0:ℝ) < (n : ℝ) := by linarith
  have hDeq : (4 * (n : ℝ))⁻¹ - Real.log 2 + ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹
      = (4 * (n : ℝ))⁻¹ - T n := by
    rw [Icc_sum n]
    have := T_eq n
    linarith
  have hInt : (a n : ℤ) =
      ⌊ 1 / ((4 * (n : ℝ))⁻¹ - Real.log 2 +
        ∑ k ∈ Finset.Icc (n + 1) (2 * n), ((k : ℝ))⁻¹) ⌋ := by
    have ha : (a n : ℤ) = 16 * (n : ℤ) ^ 2 + 1 := by
      simp only [a]
      push_cast
      ring
    rw [ha, hDeq]
    obtain ⟨hTl, hTu⟩ := T_bounds n hn1
    have hw1 := window_low (n : ℝ) hx1
    have hw2 := window_high (n : ℝ) hx1
    have hp1 : (0:ℝ) < 16 * (n : ℝ) ^ 2 + 1 := by positivity
    have hp2 : (0:ℝ) < 16 * (n : ℝ) ^ 2 + 2 := by positivity
    set D : ℝ := (4 * (n : ℝ))⁻¹ - T n with hD
    have hlow : (16 * (n : ℝ) ^ 2 + 2)⁻¹ < D := by rw [hD]; linarith
    have hhigh : D < (16 * (n : ℝ) ^ 2 + 1)⁻¹ := by rw [hD]; linarith
    have hDpos : 0 < D := lt_trans (by positivity) hlow
    have hA : (16 * (n : ℝ) ^ 2 + 1) * D < 1 := by
      have h := mul_lt_mul_of_pos_left hhigh hp1
      rwa [mul_inv_cancel₀ (ne_of_gt hp1)] at h
    have hB : 1 < (16 * (n : ℝ) ^ 2 + 2) * D := by
      have h := mul_lt_mul_of_pos_left hlow hp2
      rwa [mul_inv_cancel₀ (ne_of_gt hp2)] at h
    symm
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      rw [le_div_iff₀ hDpos]
      linarith
    · push_cast
      rw [div_lt_iff₀ hDpos]
      linarith
  exact_mod_cast hInt

end OeisA108211
