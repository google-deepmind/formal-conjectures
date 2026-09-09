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
# Nearest integer to $n/\sqrt{2}$

Nearest integer to $n/\sqrt{2}$, defined by $\lfloor n/\sqrt{2} + 1/2 \rfloor$.

*References:*
- [A049473](https://oeis.org/A049473)-/

namespace OeisA49473

/-- Nearest integer to $n/\sqrt{2}$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor ((n : ℝ) / Real.sqrt 2 + 1 / 2)).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  dsimp [a]
  have h : ((0 : ℕ) : ℝ) / Real.sqrt 2 + 1 / 2 = (1 / 2 : ℝ) := by
    simp
  rw [h]
  have hf : Int.floor (1 / 2 : ℝ) = 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  rw [hf]
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h1]
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : Int.floor ((1 : ℝ) / Real.sqrt 2 + 1 / 2) = 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      have : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 2 := by
        rw [div_le_div_iff₀ (by norm_num) h_sqrt_pos]
        linarith
      linarith
    · have hlt : (2 / 3 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have : 1 / Real.sqrt 2 < (3 / 2 : ℝ) := by
        rw [div_lt_iff₀ h_sqrt_pos]
        linarith
      linarith
  rw [hf]
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  unfold a
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : Int.floor ((2 : ℝ) / Real.sqrt 2 + 1 / 2) = 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : Real.sqrt 2 ≤ 4 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      have : (1 / 2 : ℝ) ≤ 2 / Real.sqrt 2 := by
        rw [div_le_div_iff₀ (by norm_num) h_sqrt_pos]
        linarith
      linarith
    · have hlt : (4 / 3 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have : 2 / Real.sqrt 2 < (3 / 2 : ℝ) := by
        rw [div_lt_iff₀ h_sqrt_pos]
        linarith
      linarith
  rw [hf]
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  unfold a
  have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3]
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : Int.floor ((3 : ℝ) / Real.sqrt 2 + 1 / 2) = 2 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      have : (3 / 2 : ℝ) ≤ 3 / Real.sqrt 2 := by
        rw [div_le_div_iff₀ (by norm_num) h_sqrt_pos]
        linarith
      linarith
    · have hlt : (6 / 5 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have : 3 / Real.sqrt 2 < (5 / 2 : ℝ) := by
        rw [div_lt_iff₀ h_sqrt_pos]
        linarith
      linarith
  rw [hf]
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  unfold a
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h4]
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : Int.floor ((4 : ℝ) / Real.sqrt 2 + 1 / 2) = 3 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : Real.sqrt 2 ≤ 8 / 5 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      have : (5 / 2 : ℝ) ≤ 4 / Real.sqrt 2 := by
        rw [div_le_div_iff₀ (by norm_num) h_sqrt_pos]
        linarith
      linarith
    · have hlt : (8 / 7 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have : 4 / Real.sqrt 2 < (7 / 2 : ℝ) := by
        rw [div_lt_iff₀ h_sqrt_pos]
        linarith
      linarith
  rw [hf]
  rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by
  unfold a
  have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  rw [h5]
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : Int.floor ((5 : ℝ) / Real.sqrt 2 + 1 / 2) = 4 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hle : Real.sqrt 2 ≤ 10 / 7 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      have : (7 / 2 : ℝ) ≤ 5 / Real.sqrt 2 := by
        rw [div_le_div_iff₀ (by norm_num) h_sqrt_pos]
        linarith
      linarith
    · have hlt : (10 / 9 : ℝ) < Real.sqrt 2 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have : 5 / Real.sqrt 2 < (9 / 2 : ℝ) := by
        rw [div_lt_iff₀ h_sqrt_pos]
        linarith
      linarith
  rw [hf]
  rfl

/-- $\zeta(3)$ (Apéry's constant). -/
noncomputable def zetaThreeReal : ℝ :=
  (riemannZeta 3).re

/-- Let $s(n) = \zeta(3) - \sum_{k=1}^{n} 1/k^3$. -/
noncomputable def s (n : ℕ) : ℝ :=
  zetaThreeReal - ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℝ) ^ 3)

/-- A001953: Nonhomogeneous Beatty sequence $\lfloor (k + 1/2)\sqrt{2} \rfloor$ for $k \ge 0$. -/
def A001953 : Set ℕ :=
  {n | ∃ k : ℕ, n = (Int.floor (((k : ℝ) + 1 / 2) * Real.sqrt 2)).toNat}

/-- A001954: Nonhomogeneous Beatty sequence $\lfloor (k + 1/2)(2 + \sqrt{2}) \rfloor$ for $k \ge 0$. -/
def A001954 : Set ℕ :=
  {n | ∃ k : ℕ, n = (Int.floor (((k : ℝ) + 1 / 2) * (2 + Real.sqrt 2))).toNat}

/--
Let $s(n) = \zeta(3) - \sum_{k=1}^n \frac{1}{k^3}$.
Conjecture: for $n \ge 1$, $s(a(n)) < \frac{1}{n^2} < s(a(n)-1)$, and the difference sequence of
A049473 consists solely of $0$'s and $1$'s, in positions given by the nonhomogeneous Beatty
sequences A001954 and A001953, respectively.
- Clark Kimberling, Oct 05 2014
-/
@[category research open, AMS 11]
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      let diff : ℕ := a n - a (n - 1)
      (diff = 0 ↔ n - 1 ∈ A001954) ∧ (diff = 1 ↔ n - 1 ∈ A001953)) := by
  sorry

end OeisA49473
