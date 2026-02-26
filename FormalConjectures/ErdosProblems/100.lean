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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 100
*References:*
* [erdosproblems.com/100](https://www.erdosproblems.com/100)
* [Kanold](No references found)
* [GuKa15](Guth, Larry and Katz, Nets Hawk, On the Erd\H{o}s distinct distances problem in the plane. Ann. of Math. (2) (2015), 155-190.)
* [Piepmeyer](No references found)
-/

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Set Metric Filter Real
open scoped EuclideanGeometry

namespace Erdos100

/-- If two distances in A differ, they differ by at least 1. -/
def DistancesSeparated (A : Finset ℝ²) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- Is the diameter of $A$ at least $Cn$ for some constant $C > 0$? -/
@[category research open, AMS 52]
theorem erdos_100 :
    answer(sorry) ↔ ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) > C * n := by
  sorry

/-- Stronger conjecture: diameter $\geq n - 1$ for sufficiently large $n$. -/
@[category research open, AMS 52]
theorem erdos_100_strong :
    ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ n - 1 := by
  sorry

/-- From [Kanold]: diameter $\geq n^{3/4}$.
TODO: find reference -/
@[category research open, AMS 52]
theorem erdos_100_kanold :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ (n : ℝ) ^ (3 / 4 : ℝ) := by
  sorry

/-- From [GuKa15]: diameter $\gg n / \log n$. -/
@[category research open, AMS 52]
theorem erdos_100_guth_katz :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ C * n / log n := by
  sorry

lemma dist_sq_eq_sum (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
  have hd : dist p q = Real.sqrt (∑ i, dist (p i) (q i) ^ 2) := by
    exact EuclideanSpace.dist_eq p q
  rw [hd]
  have hpos : 0 ≤ ∑ i, dist (p i) (q i) ^ 2 := by positivity
  rw [Real.sq_sqrt hpos]
  have hsum : ∑ i : Fin 2, dist (p i) (q i) ^ 2 = dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2 := by
    rw [Fin.sum_univ_two]
  rw [hsum]
  have hd0 : dist (p 0) (q 0) = |p 0 - q 0| := Real.dist_eq (p 0) (q 0)
  have hd1 : dist (p 1) (q 1) = |p 1 - q 1| := Real.dist_eq (p 1) (q 1)
  rw [hd0, hd1]
  have hsq0 : |p 0 - q 0| ^ 2 = (p 0 - q 0) ^ 2 := sq_abs (p 0 - q 0)
  have hsq1 : |p 1 - q 1| ^ 2 = (p 1 - q 1) ^ 2 := sq_abs (p 1 - q 1)
  rw [hsq0, hsq1]

noncomputable def s2 : ℝ := Real.sqrt 2
noncomputable def s3 : ℝ := Real.sqrt 3
noncomputable def s6 : ℝ := Real.sqrt 6

lemma s2_pos : 0 ≤ (2 : ℝ) := by norm_num
lemma s3_pos : 0 ≤ (3 : ℝ) := by norm_num
lemma s6_pos : 0 ≤ (6 : ℝ) := by norm_num

@[simp] lemma s2_s2 : s2 * s2 = 2 := by
  dsimp [s2]; rw [←Real.sqrt_mul s2_pos]; norm_num
@[simp] lemma s3_s3 : s3 * s3 = 3 := by
  dsimp [s3]; rw [←Real.sqrt_mul s3_pos]; norm_num
@[simp] lemma s6_s6 : s6 * s6 = 6 := by
  dsimp [s6]; rw [←Real.sqrt_mul s6_pos]; norm_num

@[simp] lemma s2_s3 : s2 * s3 = s6 := by
  dsimp [s2, s3, s6]; rw [←Real.sqrt_mul s2_pos]; norm_num
@[simp] lemma s3_s2 : s3 * s2 = s6 := by rw [mul_comm, s2_s3]
@[simp] lemma s2_s6 : s2 * s6 = 2 * s3 := by rw [←s2_s3, ←mul_assoc, s2_s2]
@[simp] lemma s6_s2 : s6 * s2 = 2 * s3 := by rw [mul_comm, s2_s6]
@[simp] lemma s3_s6 : s3 * s6 = 3 * s2 := by rw [←s2_s3, mul_comm s2 s3, ←mul_assoc, s3_s3]
@[simp] lemma s6_s3 : s6 * s3 = 3 * s2 := by rw [mul_comm, s3_s6]

@[simp] lemma s2_s2_x (x : ℝ) : s2 * (s2 * x) = 2 * x := by rw [←mul_assoc, s2_s2]
@[simp] lemma s3_s3_x (x : ℝ) : s3 * (s3 * x) = 3 * x := by rw [←mul_assoc, s3_s3]
@[simp] lemma s6_s6_x (x : ℝ) : s6 * (s6 * x) = 6 * x := by rw [←mul_assoc, s6_s6]

@[simp] lemma s2_s3_x (x : ℝ) : s2 * (s3 * x) = s6 * x := by rw [←mul_assoc, s2_s3]
@[simp] lemma s3_s2_x (x : ℝ) : s3 * (s2 * x) = s6 * x := by rw [←mul_assoc, s3_s2]
@[simp] lemma s2_s6_x (x : ℝ) : s2 * (s6 * x) = 2 * (s3 * x) := by rw [←mul_assoc, s2_s6, mul_assoc]
@[simp] lemma s6_s2_x (x : ℝ) : s6 * (s2 * x) = 2 * (s3 * x) := by rw [←mul_assoc, s6_s2, mul_assoc]
@[simp] lemma s3_s6_x (x : ℝ) : s3 * (s6 * x) = 3 * (s2 * x) := by rw [←mul_assoc, s3_s6, mul_assoc]
@[simp] lemma s6_s3_x (x : ℝ) : s6 * (s3 * x) = 3 * (s2 * x) := by rw [←mul_assoc, s6_s3, mul_assoc]

@[simp] lemma s2_sq : s2 ^ 2 = 2 := by rw [sq, s2_s2]
@[simp] lemma s3_sq : s3 ^ 2 = 3 := by rw [sq, s3_s3]
@[simp] lemma s6_sq : s6 ^ 2 = 6 := by rw [sq, s6_s6]

lemma s2_lower : 1414 / 1000 < s2 := by
  have : (1414 / 1000 : ℝ)^2 < 2 := by norm_num
  exact Real.lt_sqrt_of_sq_lt this

lemma s2_upper : s2 < 1415 / 1000 := by
  have h1 : (0:ℝ) ≤ 1415 / 1000 := by norm_num
  have h2 : (2:ℝ) < (1415 / 1000 : ℝ)^2 := by norm_num
  have h3 : Real.sqrt 2 < Real.sqrt ((1415 / 1000 : ℝ)^2) := Real.sqrt_lt_sqrt s2_pos h2
  rwa [Real.sqrt_sq h1] at h3

lemma s3_lower : 1732 / 1000 < s3 := by
  have : (1732 / 1000 : ℝ)^2 < 3 := by norm_num
  exact Real.lt_sqrt_of_sq_lt this

lemma s3_upper : s3 < 1733 / 1000 := by
  have h1 : (0:ℝ) ≤ 1733 / 1000 := by norm_num
  have h2 : (3:ℝ) < (1733 / 1000 : ℝ)^2 := by norm_num
  have h3 : Real.sqrt 3 < Real.sqrt ((1733 / 1000 : ℝ)^2) := Real.sqrt_lt_sqrt s3_pos h2
  rwa [Real.sqrt_sq h1] at h3

lemma s6_lower : 2449 / 1000 < s6 := by
  have : (2449 / 1000 : ℝ)^2 < 6 := by norm_num
  exact Real.lt_sqrt_of_sq_lt this

lemma s6_upper : s6 < 2450 / 1000 := by
  have h1 : (0:ℝ) ≤ 2450 / 1000 := by norm_num
  have h2 : (6:ℝ) < (2450 / 1000 : ℝ)^2 := by norm_num
  have h3 : Real.sqrt 6 < Real.sqrt ((2450 / 1000 : ℝ)^2) := Real.sqrt_lt_sqrt s6_pos h2
  rwa [Real.sqrt_sq h1] at h3

noncomputable def d1_sq : ℝ := 6 - 3*s3 + 4*s2 - 2*s6
noncomputable def d2_sq : ℝ := 3 + 2*s2
noncomputable def d3_sq : ℝ := 6 + 4*s2
noncomputable def d4_sq : ℝ := 6 + 3*s3 + 4*s2 + 2*s6

noncomputable def P1x : ℝ := 0
noncomputable def P1y : ℝ := (3*s2 - s6 + 6 - 2*s3) / 6
noncomputable def P2x : ℝ := -(s6 - s2 + 2*s3 - 2) / 4
noncomputable def P2y : ℝ := -(3*s2 - s6 + 6 - 2*s3) / 12
noncomputable def P3x : ℝ := (s6 - s2 + 2*s3 - 2) / 4
noncomputable def P3y : ℝ := -(3*s2 - s6 + 6 - 2*s3) / 12
noncomputable def P4x : ℝ := 0
noncomputable def P4y : ℝ := (2*s3 + s6) / 3
noncomputable def P5x : ℝ := -(2 + s2) / 2
noncomputable def P5y : ℝ := -(2*s3 + s6) / 6
noncomputable def P6x : ℝ := (2 + s2) / 2
noncomputable def P6y : ℝ := -(2*s3 + s6) / 6
noncomputable def P7x : ℝ := 0
noncomputable def P7y : ℝ := -(s6 + 3*s2 + 6 + 2*s3) / 6
noncomputable def P8x : ℝ := (3*s2 + 3*s6 + 6*s3 + 6) / 12
noncomputable def P8y : ℝ := (s6 + 3*s2 + 6 + 2*s3) / 12
noncomputable def P9x : ℝ := -(3*s2 + 3*s6 + 6*s3 + 6) / 12
noncomputable def P9y : ℝ := (s6 + 3*s2 + 6 + 2*s3) / 12

noncomputable def P1 : ℝ² := !₂[P1x, P1y]
noncomputable def P2 : ℝ² := !₂[P2x, P2y]
noncomputable def P3 : ℝ² := !₂[P3x, P3y]
noncomputable def P4 : ℝ² := !₂[P4x, P4y]
noncomputable def P5 : ℝ² := !₂[P5x, P5y]
noncomputable def P6 : ℝ² := !₂[P6x, P6y]
noncomputable def P7 : ℝ² := !₂[P7x, P7y]
noncomputable def P8 : ℝ² := !₂[P8x, P8y]
noncomputable def P9 : ℝ² := !₂[P9x, P9y]

lemma dist_sq_P1_P2 : dist P1 P2 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P2 0 = P2x := rfl
  have h1_2 : P2 1 = P2y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P2x, P2y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P3 : dist P1 P3 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P3 0 = P3x := rfl
  have h1_2 : P3 1 = P3y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P3x, P3y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P4 : dist P1 P4 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P4 0 = P4x := rfl
  have h1_2 : P4 1 = P4y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P4x, P4y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P5 : dist P1 P5 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P5 0 = P5x := rfl
  have h1_2 : P5 1 = P5y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P5x, P5y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P6 : dist P1 P6 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P6 0 = P6x := rfl
  have h1_2 : P6 1 = P6y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P6x, P6y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P7 : dist P1 P7 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P7x, P7y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P8 : dist P1 P8 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P8x, P8y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P1_P9 : dist P1 P9 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P1 0 = P1x := rfl
  have h1_1 : P1 1 = P1y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P1x, P1y, P9x, P9y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P3 : dist P2 P3 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P3 0 = P3x := rfl
  have h1_2 : P3 1 = P3y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P3x, P3y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P4 : dist P2 P4 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P4 0 = P4x := rfl
  have h1_2 : P4 1 = P4y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P4x, P4y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P5 : dist P2 P5 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P5 0 = P5x := rfl
  have h1_2 : P5 1 = P5y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P5x, P5y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P6 : dist P2 P6 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P6 0 = P6x := rfl
  have h1_2 : P6 1 = P6y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P6x, P6y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P7 : dist P2 P7 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P7x, P7y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P8 : dist P2 P8 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P8x, P8y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P2_P9 : dist P2 P9 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P2 0 = P2x := rfl
  have h1_1 : P2 1 = P2y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P2x, P2y, P9x, P9y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P4 : dist P3 P4 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P4 0 = P4x := rfl
  have h1_2 : P4 1 = P4y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P4x, P4y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P5 : dist P3 P5 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P5 0 = P5x := rfl
  have h1_2 : P5 1 = P5y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P5x, P5y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P6 : dist P3 P6 ^ 2 = d1_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P6 0 = P6x := rfl
  have h1_2 : P6 1 = P6y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P6x, P6y, d1_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P7 : dist P3 P7 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P7x, P7y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P8 : dist P3 P8 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P8x, P8y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P3_P9 : dist P3 P9 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P3 0 = P3x := rfl
  have h1_1 : P3 1 = P3y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P3x, P3y, P9x, P9y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P4_P5 : dist P4 P5 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P4 0 = P4x := rfl
  have h1_1 : P4 1 = P4y := rfl
  have h0_2 : P5 0 = P5x := rfl
  have h1_2 : P5 1 = P5y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P4x, P4y, P5x, P5y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P4_P6 : dist P4 P6 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P4 0 = P4x := rfl
  have h1_1 : P4 1 = P4y := rfl
  have h0_2 : P6 0 = P6x := rfl
  have h1_2 : P6 1 = P6y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P4x, P4y, P6x, P6y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P4_P7 : dist P4 P7 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P4 0 = P4x := rfl
  have h1_1 : P4 1 = P4y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P4x, P4y, P7x, P7y, d4_sq]
  ring_nf; simp; ring

lemma dist_sq_P4_P8 : dist P4 P8 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P4 0 = P4x := rfl
  have h1_1 : P4 1 = P4y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P4x, P4y, P8x, P8y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P4_P9 : dist P4 P9 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P4 0 = P4x := rfl
  have h1_1 : P4 1 = P4y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P4x, P4y, P9x, P9y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P5_P6 : dist P5 P6 ^ 2 = d3_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P5 0 = P5x := rfl
  have h1_1 : P5 1 = P5y := rfl
  have h0_2 : P6 0 = P6x := rfl
  have h1_2 : P6 1 = P6y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P5x, P5y, P6x, P6y, d3_sq]
  ring_nf; simp; ring

lemma dist_sq_P5_P7 : dist P5 P7 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P5 0 = P5x := rfl
  have h1_1 : P5 1 = P5y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P5x, P5y, P7x, P7y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P5_P8 : dist P5 P8 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P5 0 = P5x := rfl
  have h1_1 : P5 1 = P5y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P5x, P5y, P8x, P8y, d4_sq]
  ring_nf; simp; ring

lemma dist_sq_P5_P9 : dist P5 P9 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P5 0 = P5x := rfl
  have h1_1 : P5 1 = P5y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P5x, P5y, P9x, P9y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P6_P7 : dist P6 P7 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P6 0 = P6x := rfl
  have h1_1 : P6 1 = P6y := rfl
  have h0_2 : P7 0 = P7x := rfl
  have h1_2 : P7 1 = P7y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P6x, P6y, P7x, P7y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P6_P8 : dist P6 P8 ^ 2 = d2_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P6 0 = P6x := rfl
  have h1_1 : P6 1 = P6y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P6x, P6y, P8x, P8y, d2_sq]
  ring_nf; simp; ring

lemma dist_sq_P6_P9 : dist P6 P9 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P6 0 = P6x := rfl
  have h1_1 : P6 1 = P6y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P6x, P6y, P9x, P9y, d4_sq]
  ring_nf; simp; ring

lemma dist_sq_P7_P8 : dist P7 P8 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P7 0 = P7x := rfl
  have h1_1 : P7 1 = P7y := rfl
  have h0_2 : P8 0 = P8x := rfl
  have h1_2 : P8 1 = P8y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P7x, P7y, P8x, P8y, d4_sq]
  ring_nf; simp; ring

lemma dist_sq_P7_P9 : dist P7 P9 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P7 0 = P7x := rfl
  have h1_1 : P7 1 = P7y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P7x, P7y, P9x, P9y, d4_sq]
  ring_nf; simp; ring

lemma dist_sq_P8_P9 : dist P8 P9 ^ 2 = d4_sq := by
  rw [dist_sq_eq_sum]
  have h0_1 : P8 0 = P8x := rfl
  have h1_1 : P8 1 = P8y := rfl
  have h0_2 : P9 0 = P9x := rfl
  have h1_2 : P9 1 = P9y := rfl
  rw [h0_1, h1_1, h0_2, h1_2]
  dsimp [P8x, P8y, P9x, P9y, d4_sq]
  ring_nf; simp; ring


lemma d1_sq_pos : 0 < d1_sq := by
  dsimp [d1_sq]
  nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]

lemma d2_sq_pos : 0 < d2_sq := by
  dsimp [d2_sq]
  nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]

lemma d3_sq_pos : 0 < d3_sq := by
  dsimp [d3_sq]
  nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]

lemma d4_sq_pos : 0 < d4_sq := by
  dsimp [d4_sq]
  nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
lemma dist_P1_P2_eq : dist P1 P2 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P1 P2 := dist_nonneg
  calc
    dist P1 P2 = Real.sqrt (dist P1 P2 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P1_P2]

lemma dist_P2_P1_eq : dist P2 P1 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P1_P2_eq

lemma P1_ne_P2 : P1 ≠ P2 := by
  intro h
  have h0 : dist P1 P2 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P2 = Real.sqrt d1_sq := dist_P1_P2_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P2_ne_P1 : P2 ≠ P1 := P1_ne_P2.symm

lemma dist_P1_P3_eq : dist P1 P3 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P1 P3 := dist_nonneg
  calc
    dist P1 P3 = Real.sqrt (dist P1 P3 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P1_P3]

lemma dist_P3_P1_eq : dist P3 P1 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P1_P3_eq

lemma P1_ne_P3 : P1 ≠ P3 := by
  intro h
  have h0 : dist P1 P3 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P3 = Real.sqrt d1_sq := dist_P1_P3_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P3_ne_P1 : P3 ≠ P1 := P1_ne_P3.symm

lemma dist_P1_P4_eq : dist P1 P4 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P1 P4 := dist_nonneg
  calc
    dist P1 P4 = Real.sqrt (dist P1 P4 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P1_P4]

lemma dist_P4_P1_eq : dist P4 P1 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P1_P4_eq

lemma P1_ne_P4 : P1 ≠ P4 := by
  intro h
  have h0 : dist P1 P4 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P4 = Real.sqrt d1_sq := dist_P1_P4_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P4_ne_P1 : P4 ≠ P1 := P1_ne_P4.symm

lemma dist_P1_P5_eq : dist P1 P5 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P1 P5 := dist_nonneg
  calc
    dist P1 P5 = Real.sqrt (dist P1 P5 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P1_P5]

lemma dist_P5_P1_eq : dist P5 P1 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P1_P5_eq

lemma P1_ne_P5 : P1 ≠ P5 := by
  intro h
  have h0 : dist P1 P5 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P5 = Real.sqrt d2_sq := dist_P1_P5_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P5_ne_P1 : P5 ≠ P1 := P1_ne_P5.symm

lemma dist_P1_P6_eq : dist P1 P6 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P1 P6 := dist_nonneg
  calc
    dist P1 P6 = Real.sqrt (dist P1 P6 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P1_P6]

lemma dist_P6_P1_eq : dist P6 P1 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P1_P6_eq

lemma P1_ne_P6 : P1 ≠ P6 := by
  intro h
  have h0 : dist P1 P6 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P6 = Real.sqrt d2_sq := dist_P1_P6_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P6_ne_P1 : P6 ≠ P1 := P1_ne_P6.symm

lemma dist_P1_P7_eq : dist P1 P7 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P1 P7 := dist_nonneg
  calc
    dist P1 P7 = Real.sqrt (dist P1 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P1_P7]

lemma dist_P7_P1_eq : dist P7 P1 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P1_P7_eq

lemma P1_ne_P7 : P1 ≠ P7 := by
  intro h
  have h0 : dist P1 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P7 = Real.sqrt d3_sq := dist_P1_P7_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P1 : P7 ≠ P1 := P1_ne_P7.symm

lemma dist_P1_P8_eq : dist P1 P8 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P1 P8 := dist_nonneg
  calc
    dist P1 P8 = Real.sqrt (dist P1 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P1_P8]

lemma dist_P8_P1_eq : dist P8 P1 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P1_P8_eq

lemma P1_ne_P8 : P1 ≠ P8 := by
  intro h
  have h0 : dist P1 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P8 = Real.sqrt d2_sq := dist_P1_P8_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P1 : P8 ≠ P1 := P1_ne_P8.symm

lemma dist_P1_P9_eq : dist P1 P9 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P1 P9 := dist_nonneg
  calc
    dist P1 P9 = Real.sqrt (dist P1 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P1_P9]

lemma dist_P9_P1_eq : dist P9 P1 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P1_P9_eq

lemma P1_ne_P9 : P1 ≠ P9 := by
  intro h
  have h0 : dist P1 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P1 P9 = Real.sqrt d2_sq := dist_P1_P9_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P1 : P9 ≠ P1 := P1_ne_P9.symm

lemma dist_P2_P3_eq : dist P2 P3 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P2 P3 := dist_nonneg
  calc
    dist P2 P3 = Real.sqrt (dist P2 P3 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P2_P3]

lemma dist_P3_P2_eq : dist P3 P2 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P2_P3_eq

lemma P2_ne_P3 : P2 ≠ P3 := by
  intro h
  have h0 : dist P2 P3 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P3 = Real.sqrt d1_sq := dist_P2_P3_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P3_ne_P2 : P3 ≠ P2 := P2_ne_P3.symm

lemma dist_P2_P4_eq : dist P2 P4 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P2 P4 := dist_nonneg
  calc
    dist P2 P4 = Real.sqrt (dist P2 P4 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P2_P4]

lemma dist_P4_P2_eq : dist P4 P2 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P2_P4_eq

lemma P2_ne_P4 : P2 ≠ P4 := by
  intro h
  have h0 : dist P2 P4 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P4 = Real.sqrt d2_sq := dist_P2_P4_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P4_ne_P2 : P4 ≠ P2 := P2_ne_P4.symm

lemma dist_P2_P5_eq : dist P2 P5 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P2 P5 := dist_nonneg
  calc
    dist P2 P5 = Real.sqrt (dist P2 P5 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P2_P5]

lemma dist_P5_P2_eq : dist P5 P2 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P2_P5_eq

lemma P2_ne_P5 : P2 ≠ P5 := by
  intro h
  have h0 : dist P2 P5 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P5 = Real.sqrt d1_sq := dist_P2_P5_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P5_ne_P2 : P5 ≠ P2 := P2_ne_P5.symm

lemma dist_P2_P6_eq : dist P2 P6 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P2 P6 := dist_nonneg
  calc
    dist P2 P6 = Real.sqrt (dist P2 P6 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P2_P6]

lemma dist_P6_P2_eq : dist P6 P2 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P2_P6_eq

lemma P2_ne_P6 : P2 ≠ P6 := by
  intro h
  have h0 : dist P2 P6 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P6 = Real.sqrt d2_sq := dist_P2_P6_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P6_ne_P2 : P6 ≠ P2 := P2_ne_P6.symm

lemma dist_P2_P7_eq : dist P2 P7 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P2 P7 := dist_nonneg
  calc
    dist P2 P7 = Real.sqrt (dist P2 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P2_P7]

lemma dist_P7_P2_eq : dist P7 P2 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P2_P7_eq

lemma P2_ne_P7 : P2 ≠ P7 := by
  intro h
  have h0 : dist P2 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P7 = Real.sqrt d2_sq := dist_P2_P7_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P2 : P7 ≠ P2 := P2_ne_P7.symm

lemma dist_P2_P8_eq : dist P2 P8 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P2 P8 := dist_nonneg
  calc
    dist P2 P8 = Real.sqrt (dist P2 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P2_P8]

lemma dist_P8_P2_eq : dist P8 P2 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P2_P8_eq

lemma P2_ne_P8 : P2 ≠ P8 := by
  intro h
  have h0 : dist P2 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P8 = Real.sqrt d3_sq := dist_P2_P8_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P2 : P8 ≠ P2 := P2_ne_P8.symm

lemma dist_P2_P9_eq : dist P2 P9 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P2 P9 := dist_nonneg
  calc
    dist P2 P9 = Real.sqrt (dist P2 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P2_P9]

lemma dist_P9_P2_eq : dist P9 P2 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P2_P9_eq

lemma P2_ne_P9 : P2 ≠ P9 := by
  intro h
  have h0 : dist P2 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P2 P9 = Real.sqrt d2_sq := dist_P2_P9_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P2 : P9 ≠ P2 := P2_ne_P9.symm

lemma dist_P3_P4_eq : dist P3 P4 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P3 P4 := dist_nonneg
  calc
    dist P3 P4 = Real.sqrt (dist P3 P4 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P3_P4]

lemma dist_P4_P3_eq : dist P4 P3 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P3_P4_eq

lemma P3_ne_P4 : P3 ≠ P4 := by
  intro h
  have h0 : dist P3 P4 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P4 = Real.sqrt d2_sq := dist_P3_P4_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P4_ne_P3 : P4 ≠ P3 := P3_ne_P4.symm

lemma dist_P3_P5_eq : dist P3 P5 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P3 P5 := dist_nonneg
  calc
    dist P3 P5 = Real.sqrt (dist P3 P5 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P3_P5]

lemma dist_P5_P3_eq : dist P5 P3 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P3_P5_eq

lemma P3_ne_P5 : P3 ≠ P5 := by
  intro h
  have h0 : dist P3 P5 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P5 = Real.sqrt d2_sq := dist_P3_P5_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P5_ne_P3 : P5 ≠ P3 := P3_ne_P5.symm

lemma dist_P3_P6_eq : dist P3 P6 = Real.sqrt d1_sq := by
  have hpos : 0 ≤ dist P3 P6 := dist_nonneg
  calc
    dist P3 P6 = Real.sqrt (dist P3 P6 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d1_sq := by rw [dist_sq_P3_P6]

lemma dist_P6_P3_eq : dist P6 P3 = Real.sqrt d1_sq := by
  rw [dist_comm]; exact dist_P3_P6_eq

lemma P3_ne_P6 : P3 ≠ P6 := by
  intro h
  have h0 : dist P3 P6 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P6 = Real.sqrt d1_sq := dist_P3_P6_eq
  have h2 : 0 < Real.sqrt d1_sq := Real.sqrt_pos.mpr d1_sq_pos
  rw [h0] at h1
  linarith

lemma P6_ne_P3 : P6 ≠ P3 := P3_ne_P6.symm

lemma dist_P3_P7_eq : dist P3 P7 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P3 P7 := dist_nonneg
  calc
    dist P3 P7 = Real.sqrt (dist P3 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P3_P7]

lemma dist_P7_P3_eq : dist P7 P3 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P3_P7_eq

lemma P3_ne_P7 : P3 ≠ P7 := by
  intro h
  have h0 : dist P3 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P7 = Real.sqrt d2_sq := dist_P3_P7_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P3 : P7 ≠ P3 := P3_ne_P7.symm

lemma dist_P3_P8_eq : dist P3 P8 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P3 P8 := dist_nonneg
  calc
    dist P3 P8 = Real.sqrt (dist P3 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P3_P8]

lemma dist_P8_P3_eq : dist P8 P3 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P3_P8_eq

lemma P3_ne_P8 : P3 ≠ P8 := by
  intro h
  have h0 : dist P3 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P8 = Real.sqrt d2_sq := dist_P3_P8_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P3 : P8 ≠ P3 := P3_ne_P8.symm

lemma dist_P3_P9_eq : dist P3 P9 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P3 P9 := dist_nonneg
  calc
    dist P3 P9 = Real.sqrt (dist P3 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P3_P9]

lemma dist_P9_P3_eq : dist P9 P3 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P3_P9_eq

lemma P3_ne_P9 : P3 ≠ P9 := by
  intro h
  have h0 : dist P3 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P3 P9 = Real.sqrt d3_sq := dist_P3_P9_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P3 : P9 ≠ P3 := P3_ne_P9.symm

lemma dist_P4_P5_eq : dist P4 P5 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P4 P5 := dist_nonneg
  calc
    dist P4 P5 = Real.sqrt (dist P4 P5 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P4_P5]

lemma dist_P5_P4_eq : dist P5 P4 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P4_P5_eq

lemma P4_ne_P5 : P4 ≠ P5 := by
  intro h
  have h0 : dist P4 P5 = 0 := by rw [h, dist_self]
  have h1 : dist P4 P5 = Real.sqrt d3_sq := dist_P4_P5_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P5_ne_P4 : P5 ≠ P4 := P4_ne_P5.symm

lemma dist_P4_P6_eq : dist P4 P6 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P4 P6 := dist_nonneg
  calc
    dist P4 P6 = Real.sqrt (dist P4 P6 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P4_P6]

lemma dist_P6_P4_eq : dist P6 P4 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P4_P6_eq

lemma P4_ne_P6 : P4 ≠ P6 := by
  intro h
  have h0 : dist P4 P6 = 0 := by rw [h, dist_self]
  have h1 : dist P4 P6 = Real.sqrt d3_sq := dist_P4_P6_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P6_ne_P4 : P6 ≠ P4 := P4_ne_P6.symm

lemma dist_P4_P7_eq : dist P4 P7 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P4 P7 := dist_nonneg
  calc
    dist P4 P7 = Real.sqrt (dist P4 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P4_P7]

lemma dist_P7_P4_eq : dist P7 P4 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P4_P7_eq

lemma P4_ne_P7 : P4 ≠ P7 := by
  intro h
  have h0 : dist P4 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P4 P7 = Real.sqrt d4_sq := dist_P4_P7_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P4 : P7 ≠ P4 := P4_ne_P7.symm

lemma dist_P4_P8_eq : dist P4 P8 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P4 P8 := dist_nonneg
  calc
    dist P4 P8 = Real.sqrt (dist P4 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P4_P8]

lemma dist_P8_P4_eq : dist P8 P4 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P4_P8_eq

lemma P4_ne_P8 : P4 ≠ P8 := by
  intro h
  have h0 : dist P4 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P4 P8 = Real.sqrt d2_sq := dist_P4_P8_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P4 : P8 ≠ P4 := P4_ne_P8.symm

lemma dist_P4_P9_eq : dist P4 P9 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P4 P9 := dist_nonneg
  calc
    dist P4 P9 = Real.sqrt (dist P4 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P4_P9]

lemma dist_P9_P4_eq : dist P9 P4 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P4_P9_eq

lemma P4_ne_P9 : P4 ≠ P9 := by
  intro h
  have h0 : dist P4 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P4 P9 = Real.sqrt d2_sq := dist_P4_P9_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P4 : P9 ≠ P4 := P4_ne_P9.symm

lemma dist_P5_P6_eq : dist P5 P6 = Real.sqrt d3_sq := by
  have hpos : 0 ≤ dist P5 P6 := dist_nonneg
  calc
    dist P5 P6 = Real.sqrt (dist P5 P6 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d3_sq := by rw [dist_sq_P5_P6]

lemma dist_P6_P5_eq : dist P6 P5 = Real.sqrt d3_sq := by
  rw [dist_comm]; exact dist_P5_P6_eq

lemma P5_ne_P6 : P5 ≠ P6 := by
  intro h
  have h0 : dist P5 P6 = 0 := by rw [h, dist_self]
  have h1 : dist P5 P6 = Real.sqrt d3_sq := dist_P5_P6_eq
  have h2 : 0 < Real.sqrt d3_sq := Real.sqrt_pos.mpr d3_sq_pos
  rw [h0] at h1
  linarith

lemma P6_ne_P5 : P6 ≠ P5 := P5_ne_P6.symm

lemma dist_P5_P7_eq : dist P5 P7 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P5 P7 := dist_nonneg
  calc
    dist P5 P7 = Real.sqrt (dist P5 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P5_P7]

lemma dist_P7_P5_eq : dist P7 P5 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P5_P7_eq

lemma P5_ne_P7 : P5 ≠ P7 := by
  intro h
  have h0 : dist P5 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P5 P7 = Real.sqrt d2_sq := dist_P5_P7_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P5 : P7 ≠ P5 := P5_ne_P7.symm

lemma dist_P5_P8_eq : dist P5 P8 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P5 P8 := dist_nonneg
  calc
    dist P5 P8 = Real.sqrt (dist P5 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P5_P8]

lemma dist_P8_P5_eq : dist P8 P5 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P5_P8_eq

lemma P5_ne_P8 : P5 ≠ P8 := by
  intro h
  have h0 : dist P5 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P5 P8 = Real.sqrt d4_sq := dist_P5_P8_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P5 : P8 ≠ P5 := P5_ne_P8.symm

lemma dist_P5_P9_eq : dist P5 P9 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P5 P9 := dist_nonneg
  calc
    dist P5 P9 = Real.sqrt (dist P5 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P5_P9]

lemma dist_P9_P5_eq : dist P9 P5 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P5_P9_eq

lemma P5_ne_P9 : P5 ≠ P9 := by
  intro h
  have h0 : dist P5 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P5 P9 = Real.sqrt d2_sq := dist_P5_P9_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P5 : P9 ≠ P5 := P5_ne_P9.symm

lemma dist_P6_P7_eq : dist P6 P7 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P6 P7 := dist_nonneg
  calc
    dist P6 P7 = Real.sqrt (dist P6 P7 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P6_P7]

lemma dist_P7_P6_eq : dist P7 P6 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P6_P7_eq

lemma P6_ne_P7 : P6 ≠ P7 := by
  intro h
  have h0 : dist P6 P7 = 0 := by rw [h, dist_self]
  have h1 : dist P6 P7 = Real.sqrt d2_sq := dist_P6_P7_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P7_ne_P6 : P7 ≠ P6 := P6_ne_P7.symm

lemma dist_P6_P8_eq : dist P6 P8 = Real.sqrt d2_sq := by
  have hpos : 0 ≤ dist P6 P8 := dist_nonneg
  calc
    dist P6 P8 = Real.sqrt (dist P6 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d2_sq := by rw [dist_sq_P6_P8]

lemma dist_P8_P6_eq : dist P8 P6 = Real.sqrt d2_sq := by
  rw [dist_comm]; exact dist_P6_P8_eq

lemma P6_ne_P8 : P6 ≠ P8 := by
  intro h
  have h0 : dist P6 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P6 P8 = Real.sqrt d2_sq := dist_P6_P8_eq
  have h2 : 0 < Real.sqrt d2_sq := Real.sqrt_pos.mpr d2_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P6 : P8 ≠ P6 := P6_ne_P8.symm

lemma dist_P6_P9_eq : dist P6 P9 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P6 P9 := dist_nonneg
  calc
    dist P6 P9 = Real.sqrt (dist P6 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P6_P9]

lemma dist_P9_P6_eq : dist P9 P6 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P6_P9_eq

lemma P6_ne_P9 : P6 ≠ P9 := by
  intro h
  have h0 : dist P6 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P6 P9 = Real.sqrt d4_sq := dist_P6_P9_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P6 : P9 ≠ P6 := P6_ne_P9.symm

lemma dist_P7_P8_eq : dist P7 P8 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P7 P8 := dist_nonneg
  calc
    dist P7 P8 = Real.sqrt (dist P7 P8 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P7_P8]

lemma dist_P8_P7_eq : dist P8 P7 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P7_P8_eq

lemma P7_ne_P8 : P7 ≠ P8 := by
  intro h
  have h0 : dist P7 P8 = 0 := by rw [h, dist_self]
  have h1 : dist P7 P8 = Real.sqrt d4_sq := dist_P7_P8_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P8_ne_P7 : P8 ≠ P7 := P7_ne_P8.symm

lemma dist_P7_P9_eq : dist P7 P9 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P7 P9 := dist_nonneg
  calc
    dist P7 P9 = Real.sqrt (dist P7 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P7_P9]

lemma dist_P9_P7_eq : dist P9 P7 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P7_P9_eq

lemma P7_ne_P9 : P7 ≠ P9 := by
  intro h
  have h0 : dist P7 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P7 P9 = Real.sqrt d4_sq := dist_P7_P9_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P7 : P9 ≠ P7 := P7_ne_P9.symm

lemma dist_P8_P9_eq : dist P8 P9 = Real.sqrt d4_sq := by
  have hpos : 0 ≤ dist P8 P9 := dist_nonneg
  calc
    dist P8 P9 = Real.sqrt (dist P8 P9 ^ 2) := (Real.sqrt_sq hpos).symm
    _ = Real.sqrt d4_sq := by rw [dist_sq_P8_P9]

lemma dist_P9_P8_eq : dist P9 P8 = Real.sqrt d4_sq := by
  rw [dist_comm]; exact dist_P8_P9_eq

lemma P8_ne_P9 : P8 ≠ P9 := by
  intro h
  have h0 : dist P8 P9 = 0 := by rw [h, dist_self]
  have h1 : dist P8 P9 = Real.sqrt d4_sq := dist_P8_P9_eq
  have h2 : 0 < Real.sqrt d4_sq := Real.sqrt_pos.mpr d4_sq_pos
  rw [h0] at h1
  linarith

lemma P9_ne_P8 : P9 ≠ P8 := P8_ne_P9.symm


noncomputable def A : Finset ℝ² := {P1, P2, P3, P4, P5, P6, P7, P8, P9}
noncomputable def D : Set ℝ := {0, Real.sqrt d1_sq, Real.sqrt d2_sq, Real.sqrt d3_sq, Real.sqrt d4_sq}

lemma in_D_P1 (q : ℝ²) (hq : q ∈ A) : dist P1 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_self]; simp [D]
  · rw [dist_P1_P2_eq]; simp [D]
  · rw [dist_P1_P3_eq]; simp [D]
  · rw [dist_P1_P4_eq]; simp [D]
  · rw [dist_P1_P5_eq]; simp [D]
  · rw [dist_P1_P6_eq]; simp [D]
  · rw [dist_P1_P7_eq]; simp [D]
  · rw [dist_P1_P8_eq]; simp [D]
  · rw [dist_P1_P9_eq]; simp [D]

lemma in_D_P2 (q : ℝ²) (hq : q ∈ A) : dist P2 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P2_P1_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P2_P3_eq]; simp [D]
  · rw [dist_P2_P4_eq]; simp [D]
  · rw [dist_P2_P5_eq]; simp [D]
  · rw [dist_P2_P6_eq]; simp [D]
  · rw [dist_P2_P7_eq]; simp [D]
  · rw [dist_P2_P8_eq]; simp [D]
  · rw [dist_P2_P9_eq]; simp [D]

lemma in_D_P3 (q : ℝ²) (hq : q ∈ A) : dist P3 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P3_P1_eq]; simp [D]
  · rw [dist_P3_P2_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P3_P4_eq]; simp [D]
  · rw [dist_P3_P5_eq]; simp [D]
  · rw [dist_P3_P6_eq]; simp [D]
  · rw [dist_P3_P7_eq]; simp [D]
  · rw [dist_P3_P8_eq]; simp [D]
  · rw [dist_P3_P9_eq]; simp [D]

lemma in_D_P4 (q : ℝ²) (hq : q ∈ A) : dist P4 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P4_P1_eq]; simp [D]
  · rw [dist_P4_P2_eq]; simp [D]
  · rw [dist_P4_P3_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P4_P5_eq]; simp [D]
  · rw [dist_P4_P6_eq]; simp [D]
  · rw [dist_P4_P7_eq]; simp [D]
  · rw [dist_P4_P8_eq]; simp [D]
  · rw [dist_P4_P9_eq]; simp [D]

lemma in_D_P5 (q : ℝ²) (hq : q ∈ A) : dist P5 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P5_P1_eq]; simp [D]
  · rw [dist_P5_P2_eq]; simp [D]
  · rw [dist_P5_P3_eq]; simp [D]
  · rw [dist_P5_P4_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P5_P6_eq]; simp [D]
  · rw [dist_P5_P7_eq]; simp [D]
  · rw [dist_P5_P8_eq]; simp [D]
  · rw [dist_P5_P9_eq]; simp [D]

lemma in_D_P6 (q : ℝ²) (hq : q ∈ A) : dist P6 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P6_P1_eq]; simp [D]
  · rw [dist_P6_P2_eq]; simp [D]
  · rw [dist_P6_P3_eq]; simp [D]
  · rw [dist_P6_P4_eq]; simp [D]
  · rw [dist_P6_P5_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P6_P7_eq]; simp [D]
  · rw [dist_P6_P8_eq]; simp [D]
  · rw [dist_P6_P9_eq]; simp [D]

lemma in_D_P7 (q : ℝ²) (hq : q ∈ A) : dist P7 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P7_P1_eq]; simp [D]
  · rw [dist_P7_P2_eq]; simp [D]
  · rw [dist_P7_P3_eq]; simp [D]
  · rw [dist_P7_P4_eq]; simp [D]
  · rw [dist_P7_P5_eq]; simp [D]
  · rw [dist_P7_P6_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P7_P8_eq]; simp [D]
  · rw [dist_P7_P9_eq]; simp [D]

lemma in_D_P8 (q : ℝ²) (hq : q ∈ A) : dist P8 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P8_P1_eq]; simp [D]
  · rw [dist_P8_P2_eq]; simp [D]
  · rw [dist_P8_P3_eq]; simp [D]
  · rw [dist_P8_P4_eq]; simp [D]
  · rw [dist_P8_P5_eq]; simp [D]
  · rw [dist_P8_P6_eq]; simp [D]
  · rw [dist_P8_P7_eq]; simp [D]
  · rw [dist_self]; simp [D]
  · rw [dist_P8_P9_eq]; simp [D]

lemma in_D_P9 (q : ℝ²) (hq : q ∈ A) : dist P9 q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P9_P1_eq]; simp [D]
  · rw [dist_P9_P2_eq]; simp [D]
  · rw [dist_P9_P3_eq]; simp [D]
  · rw [dist_P9_P4_eq]; simp [D]
  · rw [dist_P9_P5_eq]; simp [D]
  · rw [dist_P9_P6_eq]; simp [D]
  · rw [dist_P9_P7_eq]; simp [D]
  · rw [dist_P9_P8_eq]; simp [D]
  · rw [dist_self]; simp [D]


lemma in_D (p q : ℝ²) (hp : p ∈ A) (hq : q ∈ A) : dist p q ∈ D := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact in_D_P1 q hq
  · exact in_D_P2 q hq
  · exact in_D_P3 q hq
  · exact in_D_P4 q hq
  · exact in_D_P5 q hq
  · exact in_D_P6 q hq
  · exact in_D_P7 q hq
  · exact in_D_P8 q hq
  · exact in_D_P9 q hq

lemma sqrt_diff_ge_one {A B : ℝ} (hB : 0 ≤ B) (hAB : 0 ≤ A - B - 1) (h_sq : 4 * B ≤ (A - B - 1)^2) :
    Real.sqrt A - Real.sqrt B ≥ 1 := by
  have h2 : (2 * Real.sqrt B)^2 = 4 * B := by
    calc
      (2 * Real.sqrt B)^2 = 4 * (Real.sqrt B)^2 := by ring
      _ = 4 * B := by rw [Real.sq_sqrt hB]
  have h3 : (2 * Real.sqrt B)^2 ≤ (A - B - 1)^2 := by linarith
  have h4 : Real.sqrt ((2 * Real.sqrt B)^2) ≤ Real.sqrt ((A - B - 1)^2) := Real.sqrt_le_sqrt h3
  have hsB : 0 ≤ 2 * Real.sqrt B := by positivity
  rw [Real.sqrt_sq hsB, Real.sqrt_sq hAB] at h4
  have h5 : (Real.sqrt B + 1)^2 ≤ A := by
    calc
      (Real.sqrt B + 1)^2 = (Real.sqrt B)^2 + 2 * Real.sqrt B + 1 := by ring
      _ = B + 2 * Real.sqrt B + 1 := by rw [Real.sq_sqrt hB]
      _ ≤ B + (A - B - 1) + 1 := by linarith
      _ = A := by ring
  have h6 : Real.sqrt ((Real.sqrt B + 1)^2) ≤ Real.sqrt A := Real.sqrt_le_sqrt h5
  have h7 : 0 ≤ Real.sqrt B + 1 := by positivity
  rw [Real.sqrt_sq h7] at h6
  linarith

lemma h1 : 1 ≤ Real.sqrt d1_sq := by
  have : (1:ℝ) ≤ d1_sq := by
    dsimp [d1_sq]
    nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
  have h2 : Real.sqrt 1 ≤ Real.sqrt d1_sq := Real.sqrt_le_sqrt this
  rwa [Real.sqrt_one] at h2

lemma h2 : 1 ≤ Real.sqrt d2_sq - Real.sqrt d1_sq := by
  apply sqrt_diff_ge_one
  · exact le_of_lt d1_sq_pos
  · have hAB : 0 ≤ d2_sq - d1_sq - 1 := by
      dsimp [d1_sq, d2_sq]; nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    exact hAB
  · have hsq1 : (d2_sq - d1_sq - 1)^2 = 75 + 52*s2 - 40*s3 - 28*s6 := by
      dsimp [d1_sq, d2_sq]
      calc
        (3 + 2*s2 - (6 - 3*s3 + 4*s2 - 2*s6) - 1)^2 = (-4 - 2*s2 + 3*s3 + 2*s6)^2 := by ring
        _ = 75 + 52*s2 - 40*s3 - 28*s6 := by ring_nf; simp; ring
    have hsq2 : 4 * d1_sq = 24 + 16*s2 - 12*s3 - 8*s6 := by
      dsimp [d1_sq]; ring
    nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper, hsq1, hsq2]

lemma h3 : 1 ≤ Real.sqrt d3_sq - Real.sqrt d2_sq := by
  apply sqrt_diff_ge_one
  · exact le_of_lt d2_sq_pos
  · have hAB : 0 ≤ d3_sq - d2_sq - 1 := by
      dsimp [d2_sq, d3_sq]; nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    exact hAB
  · have hsq1 : (d3_sq - d2_sq - 1)^2 = 12 + 8*s2 := by
      dsimp [d2_sq, d3_sq]
      calc
        (6 + 4*s2 - (3 + 2*s2) - 1)^2 = (2 + 2*s2)^2 := by ring
        _ = 12 + 8*s2 := by ring_nf; simp; ring
    have hsq2 : 4 * d2_sq = 12 + 8*s2 := by
      dsimp [d2_sq]; ring
    rw [hsq1, hsq2]

lemma h4 : 1 ≤ Real.sqrt d4_sq - Real.sqrt d3_sq := by
  apply sqrt_diff_ge_one
  · exact le_of_lt d3_sq_pos
  · have hAB : 0 ≤ d4_sq - d3_sq - 1 := by
      dsimp [d3_sq, d4_sq]; nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    exact hAB
  · have hsq1 : (d4_sq - d3_sq - 1)^2 = 52 + 36*s2 - 6*s3 - 4*s6 := by
      dsimp [d3_sq, d4_sq]
      calc
        (6 + 3*s3 + 4*s2 + 2*s6 - (6 + 4*s2) - 1)^2 = (-1 + 3*s3 + 2*s6)^2 := by ring
        _ = 52 + 36*s2 - 6*s3 - 4*s6 := by ring_nf; simp; ring
    have hsq2 : 4 * d3_sq = 24 + 16*s2 := by
      dsimp [d3_sq]; ring
    nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper, hsq1, hsq2]

lemma h20 : 1 ≤ Real.sqrt d2_sq := by linarith [h1, h2]
lemma h30 : 1 ≤ Real.sqrt d3_sq := by linarith [h1, h2, h3]
lemma h40 : 1 ≤ Real.sqrt d4_sq := by linarith [h1, h2, h3, h4]

lemma h31 : 1 ≤ Real.sqrt d3_sq - Real.sqrt d1_sq := by linarith [h2, h3]
lemma h41 : 1 ≤ Real.sqrt d4_sq - Real.sqrt d1_sq := by linarith [h2, h3, h4]
lemma h42 : 1 ≤ Real.sqrt d4_sq - Real.sqrt d2_sq := by linarith [h3, h4]

lemma D_separated (d_a d_b : ℝ) (ha : d_a ∈ D) (hb : d_b ∈ D) (hne : d_a ≠ d_b) : |d_a - d_b| ≥ 1 := by
  dsimp [D] at ha hb
  rcases ha with rfl|rfl|rfl|rfl|rfl
  <;> rcases hb with rfl|rfl|rfl|rfl|rfl
  <;> try { contradiction }
  -- Case explicit mapping to eliminate nlinarith timeouts on 25 branches
  · rw [abs_sub_comm, sub_zero]; exact le_trans h1 (le_abs_self _)
  · rw [abs_sub_comm, sub_zero]; exact le_trans h20 (le_abs_self _)
  · rw [abs_sub_comm, sub_zero]; exact le_trans h30 (le_abs_self _)
  · rw [abs_sub_comm, sub_zero]; exact le_trans h40 (le_abs_self _)
  · rw [sub_zero]; exact le_trans h1 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h2 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h31 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h41 (le_abs_self _)
  · rw [sub_zero]; exact le_trans h20 (le_abs_self _)
  · exact le_trans h2 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h3 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h42 (le_abs_self _)
  · rw [sub_zero]; exact le_trans h30 (le_abs_self _)
  · exact le_trans h31 (le_abs_self _)
  · exact le_trans h3 (le_abs_self _)
  · rw [abs_sub_comm]; exact le_trans h4 (le_abs_self _)
  · rw [sub_zero]; exact le_trans h40 (le_abs_self _)
  · exact le_trans h41 (le_abs_self _)
  · exact le_trans h42 (le_abs_self _)
  · exact le_trans h4 (le_abs_self _)

lemma A_separated : DistancesSeparated A := by
  intro p1 q1 p2 q2 hp1 hq1 hp2 hq2 hne
  have hd1 : dist p1 q1 ∈ D := in_D p1 q1 hp1 hq1
  have hd2 : dist p2 q2 ∈ D := in_D p2 q2 hp2 hq2
  by_cases heq : dist p1 q1 = dist p2 q2
  · contradiction
  · exact D_separated _ _ hd1 hd2 heq

lemma diam_P1 (q : ℝ²) (hq : q ∈ A) : dist P1 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_self]; norm_num
  · rw [dist_P1_P2_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P3_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P4_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P5_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P6_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P7_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P8_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P1_P9_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P2 (q : ℝ²) (hq : q ∈ A) : dist P2 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P2_P1_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P2_P3_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P4_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P5_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P6_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P7_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P8_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P2_P9_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P3 (q : ℝ²) (hq : q ∈ A) : dist P3 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P3_P1_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P2_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P3_P4_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P5_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P6_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P7_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P8_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P3_P9_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P4 (q : ℝ²) (hq : q ∈ A) : dist P4 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P4_P1_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P2_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P3_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P4_P5_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P6_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P7_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P8_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P4_P9_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P5 (q : ℝ²) (hq : q ∈ A) : dist P5 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P5_P1_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P2_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P3_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P4_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P5_P6_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P7_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P8_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P5_P9_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P6 (q : ℝ²) (hq : q ∈ A) : dist P6 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P6_P1_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P2_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P3_eq]
    have h : d1_sq < (4.9 : ℝ)^2 := by
      dsimp [d1_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d1_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d1_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P4_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P5_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P6_P7_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P8_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P6_P9_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P7 (q : ℝ²) (hq : q ∈ A) : dist P7 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P7_P1_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P2_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P3_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P4_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P5_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P6_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P7_P8_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P7_P9_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P8 (q : ℝ²) (hq : q ∈ A) : dist P8 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P8_P1_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P2_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P3_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P4_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P5_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P6_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P8_P7_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num
  · rw [dist_P8_P9_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2

lemma diam_P9 (q : ℝ²) (hq : q ∈ A) : dist P9 q ≤ 4.9 := by
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [dist_P9_P1_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P2_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P3_eq]
    have h : d3_sq < (4.9 : ℝ)^2 := by
      dsimp [d3_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d3_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d3_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P4_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P5_eq]
    have h : d2_sq < (4.9 : ℝ)^2 := by
      dsimp [d2_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d2_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d2_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P6_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P7_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_P9_P8_eq]
    have h : d4_sq < (4.9 : ℝ)^2 := by
      dsimp [d4_sq]
      nlinarith [s2_lower, s2_upper, s3_lower, s3_upper, s6_lower, s6_upper]
    have h2 : Real.sqrt d4_sq < Real.sqrt ((4.9 : ℝ)^2) := Real.sqrt_lt_sqrt (le_of_lt d4_sq_pos) h
    rw [Real.sqrt_sq (by norm_num)] at h2
    exact le_of_lt h2
  · rw [dist_self]; norm_num


lemma diam_A_lt_5 : diam (A : Set ℝ²) < 5 := by
  have hdiam : diam (A : Set ℝ²) ≤ 4.9 := by
    apply Metric.diam_le_of_forall_dist_le
    · norm_num
    · intro p hp q hq
      simp only [A, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact diam_P1 q hq
      · exact diam_P2 q hq
      · exact diam_P3 q hq
      · exact diam_P4 q hq
      · exact diam_P5 q hq
      · exact diam_P6 q hq
      · exact diam_P7 q hq
      · exact diam_P8 q hq
      · exact diam_P9 q hq

  exact lt_of_le_of_lt hdiam (by norm_num)

lemma A_card : A.card = 9 := by
  dsimp [A]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P1_ne_P2, P1_ne_P3, P1_ne_P4, P1_ne_P5, P1_ne_P6, P1_ne_P7, P1_ne_P8, P1_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P2_ne_P3, P2_ne_P4, P2_ne_P5, P2_ne_P6, P2_ne_P7, P2_ne_P8, P2_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P3_ne_P4, P3_ne_P5, P3_ne_P6, P3_ne_P7, P3_ne_P8, P3_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P4_ne_P5, P4_ne_P6, P4_ne_P7, P4_ne_P8, P4_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P5_ne_P6, P5_ne_P7, P5_ne_P8, P5_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P6_ne_P7, P6_ne_P8, P6_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact ⟨P7_ne_P8, P7_ne_P9⟩)]
  rw [Finset.card_insert_of_notMem (by simp; exact P8_ne_P9)]
  simp


/-- From [Piepmeyer]: 9 points with diameter $< 5$.
TODO: find reference -/
@[category research solved, AMS 52]
@[category research formally solved using formal_conjectures at "", AMS 52]
theorem erdos_100_piepmeyer :
    ∃ A : Finset ℝ², A.card = 9 ∧ DistancesSeparated A ∧
      diam (A : Set ℝ²) < 5 := by
  use A
  exact ⟨A_card, A_separated, diam_A_lt_5⟩

end Erdos100
