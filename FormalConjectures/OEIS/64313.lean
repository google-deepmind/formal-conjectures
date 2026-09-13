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
# Integer part of area of a regular polygon with $n$ sides each of length 1

The area of a regular $n$-gon with side length 1 is given by
$\frac{n}{4} \cot(\pi / n) = \frac{n}{4 \tan(\pi / n)}$.

*References:*
- [A064313](https://oeis.org/A064313)
-/

namespace OeisA64313

/-- The exact area of a regular $n$-gon with side length 1. -/
noncomputable def area (n : ℕ) : ℝ :=
  (n : ℝ) / (4 * Real.tan (Real.pi / (n : ℝ)))

/-- Integer part of area of a regular polygon with $n$ sides each of length 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Int.floor (area n)).toNat

@[category test, AMS 51]
theorem a_1 : a 1 = 0 := by
  dsimp [a, area]
  have h : Real.pi / ((1 : ℕ) : ℝ) = Real.pi := by norm_num
  rw [h, Real.tan_pi]
  norm_num

@[category test, AMS 51]
theorem a_2 : a 2 = 0 := by
  dsimp [a, area]
  rw [Real.tan_pi_div_two]
  norm_num

@[category test, AMS 51]
theorem a_3 : a 3 = 0 := by
  dsimp [a, area]
  rw [Real.tan_pi_div_three]
  have hf : Int.floor ((3 : ℝ) / (4 * Real.sqrt 3)) = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    have h_sqrt : (1 : ℝ) < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
    constructor
    · positivity
    · have : (3 : ℝ) < 4 * Real.sqrt 3 := by linarith
      exact (div_lt_one (by positivity)).mpr this
  rw [hf]
  rfl

@[category test, AMS 51]
theorem a_4 : a 4 = 1 := by
  dsimp [a, area]
  have h : (4 : ℝ) / (4 * Real.tan (Real.pi / 4)) = 1 := by
    rw [Real.tan_pi_div_four]
    ring
  rw [h]
  have hf : Int.floor (1 : ℝ) = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  rw [hf]
  rfl

@[category test, AMS 51]
theorem a_6 : a 6 = 2 := by
  dsimp [a, area]
  rw [Real.tan_pi_div_six]
  have h_eq : (6 : ℝ) / (4 * (1 / Real.sqrt 3)) = 3 * Real.sqrt 3 / 2 := by
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    ring
  rw [h_eq]
  have hf : Int.floor (3 * Real.sqrt 3 / 2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num
    have hle : (4 / 3 : ℝ) ≤ Real.sqrt 3 := by
      have : (4 / 3 : ℝ) ^ 2 ≤ 3 := by norm_num
      exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr this
    have hlt : Real.sqrt 3 < 2 := by
      have : (3 : ℝ) < 2 ^ 2 := by norm_num
      exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr this
    constructor <;> linarith
  rw [hf]
  rfl

/--
"Usually (perhaps always?) $\lfloor n^2 / (4\pi) - \pi / 12 \rfloor$ for a polygon of circumference $n$.
Note that the area of a circle with circumference $C$ is $C^2 / (4\pi)$."
-/
@[category research open, AMS 51]
theorem conjecture (n : ℕ) (hn : 3 ≤ n) :
    a n = (Int.floor ((n : ℝ) ^ 2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  sorry

end OeisA64313
