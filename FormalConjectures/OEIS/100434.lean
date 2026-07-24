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
# OEIS A100434: auxiliary Pell-sequence identities

A100434 is the integer sequence with generating function

$$(1+x)(3+x)/(1+6x^2+x^4),$$

beginning `3, 4, -17, -24, 99, 140, ...`.

An OEIS comment records auxiliary sequences `b`, `c`, `d`, `e`, `f`, `g`,
and a final sequence called first `a` and later `h`. The surrounding prose
shows that `b` is obtained by swapping adjacent terms of `c`. Consequently,
the displayed identity `c(n) + d(n) = b(n)` is missing its alternating sign:

`c n + d n = (-1)^(n+1) * b n`.

With that correction, all three auxiliary identities hold. The name `a` is
reserved here for the primary OEIS sequence, so the final auxiliary sequence
is named `h`.

*References:*
- [OEIS A100434](https://oeis.org/A100434)
-/

namespace OeisA100434

/-- A100434, defined by the order-four recurrence from its generating function. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_2 : a 2 = -17 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_3 : a 3 = -24 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_4 : a 4 = 99 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_5 : a 5 = 140 := by
  norm_num [a]

/-- The positive Pell companion values `1, 3, 7, 17, 41, ...`. -/
def cAbs : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 2 * cAbs (n + 1) + cAbs n

/-- Half of the positive values `2, 4, 10, 24, 58, ...`. -/
def dHalfAbs : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * dHalfAbs (n + 1) + dHalfAbs n

/-- The auxiliary sequence `c` from the OEIS comment. -/
def c (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((n + 1) / 2) * cAbs n

/-- The auxiliary sequence `d` from the OEIS comment. -/
def d (n : ℕ) : ℤ :=
  2 * ((-1 : ℤ) ^ (n / 2) * dHalfAbs n)

/-- The sequence obtained by swapping consecutive terms of `c`. -/
def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then c (n + 1) else c (n - 1)

/-- The auxiliary sequence `e` from the OEIS comment. -/
def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then d n / 2 else -(d (n - 1) / 2)

/-- The auxiliary sequence `f` from the OEIS comment. -/
def f (n : ℕ) : ℤ :=
  if n % 2 = 0 then d (n + 1) / 2 else d n / 2

/-- The auxiliary sequence `g` from the OEIS comment. -/
def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0 else c n

/-- The auxiliary sequence called `a` and later `h` in the OEIS comment. -/
def h (n : ℕ) : ℤ :=
  if n % 2 = 0 then -c (n + 1) else d n

/-- The two positive Pell companion sequences differ by a first difference. -/
@[category API, AMS 11]
theorem two_mul_dHalfAbs (n : ℕ) :
    2 * dHalfAbs n = cAbs (n + 1) - cAbs n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [dHalfAbs, cAbs]
  | one => norm_num [dHalfAbs, cAbs]
  | more n hn hn1 =>
      simp only [dHalfAbs, cAbs] at hn hn1 ⊢
      nlinarith

@[category API, AMS 11]
private theorem parity_split (n : ℕ) :
    (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  omega

/--
The corrected auxiliary identities associated with OEIS A100434.

The OEIS text prints `c(n) + d(n) = b(n)`, but `b` is explicitly the
adjacent-term swap of `c`. The listed values and the surrounding explanation
therefore give the corrected final equality
`c(n) + d(n) = (-1)^(n+1) * b(n)`.

Formalized and proved by Dominic Dabish with assistance from
ProofOrchestrator using OpenAI GPT-5.6 Thinking.

*Reference:*
- [OEIS A100434](https://oeis.org/A100434)
-/
@[category research solved, AMS 11]
theorem a100434_auxiliary_identities (n : ℕ) :
    c n + d n = e n + f n ∧
    e n + f n = g n + h n ∧
    c n + d n = (-1 : ℤ) ^ (n + 1) * b n := by
  rcases parity_split n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h0 := two_mul_dHalfAbs (2 * k)
    have h1 := two_mul_dHalfAbs (2 * k + 1)
    simp only [cAbs] at h1
    have hsum :
        dHalfAbs (2 * k) + dHalfAbs (2 * k + 1) = cAbs (2 * k + 1) := by
      linarith
    have hdiff :
        dHalfAbs (2 * k + 1) - dHalfAbs (2 * k) = cAbs (2 * k) := by
      linarith
    have hc0 :
        c (2 * k) = (-1 : ℤ) ^ k * cAbs (2 * k) := by
      change (-1 : ℤ) ^ ((2 * k + 1) / 2) * cAbs (2 * k) =
        (-1 : ℤ) ^ k * cAbs (2 * k)
      rw [show (2 * k + 1) / 2 = k by omega]
    have hc1 :
        c (2 * k + 1) = -((-1 : ℤ) ^ k * cAbs (2 * k + 1)) := by
      change (-1 : ℤ) ^ ((2 * k + 1 + 1) / 2) * cAbs (2 * k + 1) =
        -((-1 : ℤ) ^ k * cAbs (2 * k + 1))
      rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, pow_succ]
      ring
    have hd0 :
        d (2 * k) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k)) := by
      change 2 * ((-1 : ℤ) ^ ((2 * k) / 2) * dHalfAbs (2 * k)) =
        2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k))
      rw [show (2 * k) / 2 = k by omega]
    have hd1 :
        d (2 * k + 1) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1)) := by
      change 2 * ((-1 : ℤ) ^ ((2 * k + 1) / 2) * dHalfAbs (2 * k + 1)) =
        2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1))
      rw [show (2 * k + 1) / 2 = k by omega]
    have he0 :
        e (2 * k) = (-1 : ℤ) ^ k * dHalfAbs (2 * k) := by
      rw [e, if_pos (by omega), hd0]
      simp
    have hf0 :
        f (2 * k) = (-1 : ℤ) ^ k * dHalfAbs (2 * k + 1) := by
      rw [f, if_pos (by omega), hd1]
      simp
    have hg0 : g (2 * k) = 0 := by
      rw [g, if_pos (by omega)]
    have hh0 :
        h (2 * k) = (-1 : ℤ) ^ k * cAbs (2 * k + 1) := by
      rw [h, if_pos (by omega), hc1]
      ring
    have hb0 :
        b (2 * k) = -((-1 : ℤ) ^ k * cAbs (2 * k + 1)) := by
      rw [b, if_pos (by omega), hc1]
    have hp0 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    constructor
    · rw [hc0, hd0, he0, hf0]
      rw [← hdiff]
      ring
    constructor
    · rw [he0, hf0, hg0, hh0, ← hsum]
      ring
    · rw [hc0, hd0, hb0, hp0, ← hdiff, ← hsum]
      ring
  · have h0 := two_mul_dHalfAbs (2 * k)
    have h1 := two_mul_dHalfAbs (2 * k + 1)
    simp only [cAbs] at h1
    have hsum :
        dHalfAbs (2 * k) + dHalfAbs (2 * k + 1) = cAbs (2 * k + 1) := by
      linarith
    have hdiff :
        dHalfAbs (2 * k + 1) - dHalfAbs (2 * k) = cAbs (2 * k) := by
      linarith
    have hc0 :
        c (2 * k) = (-1 : ℤ) ^ k * cAbs (2 * k) := by
      change (-1 : ℤ) ^ ((2 * k + 1) / 2) * cAbs (2 * k) =
        (-1 : ℤ) ^ k * cAbs (2 * k)
      rw [show (2 * k + 1) / 2 = k by omega]
    have hc1 :
        c (2 * k + 1) = -((-1 : ℤ) ^ k * cAbs (2 * k + 1)) := by
      change (-1 : ℤ) ^ ((2 * k + 1 + 1) / 2) * cAbs (2 * k + 1) =
        -((-1 : ℤ) ^ k * cAbs (2 * k + 1))
      rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, pow_succ]
      ring
    have hd0 :
        d (2 * k) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k)) := by
      change 2 * ((-1 : ℤ) ^ ((2 * k) / 2) * dHalfAbs (2 * k)) =
        2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k))
      rw [show (2 * k) / 2 = k by omega]
    have hd1 :
        d (2 * k + 1) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1)) := by
      change 2 * ((-1 : ℤ) ^ ((2 * k + 1) / 2) * dHalfAbs (2 * k + 1)) =
        2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1))
      rw [show (2 * k + 1) / 2 = k by omega]
    have he1 :
        e (2 * k + 1) = -((-1 : ℤ) ^ k * dHalfAbs (2 * k)) := by
      rw [e, if_neg (by omega)]
      rw [show 2 * k + 1 - 1 = 2 * k by omega, hd0]
      simp
    have hf1 :
        f (2 * k + 1) = (-1 : ℤ) ^ k * dHalfAbs (2 * k + 1) := by
      rw [f, if_neg (by omega), hd1]
      simp
    have hg1 :
        g (2 * k + 1) = -((-1 : ℤ) ^ k * cAbs (2 * k + 1)) := by
      rw [g, if_neg (by omega), hc1]
    have hh1 :
        h (2 * k + 1) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1)) := by
      rw [h, if_neg (by omega), hd1]
    have hb1 :
        b (2 * k + 1) = (-1 : ℤ) ^ k * cAbs (2 * k) := by
      rw [b, if_neg (by omega)]
      rw [show 2 * k + 1 - 1 = 2 * k by omega, hc0]
    have hp1 : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
      norm_num
    constructor
    · rw [hc1, hd1, he1, hf1, ← hsum]
      ring
    constructor
    · rw [he1, hf1, hg1, hh1, ← hsum]
      ring
    · rw [hc1, hd1, hb1, hp1, ← hsum, ← hdiff]
      ring

end OeisA100434
