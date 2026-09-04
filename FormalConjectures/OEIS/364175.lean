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
# Factorial ratio $\frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$

The sequence is defined for $n$ divisible by $3$ ($n = 3m$) by
$$a(n) = \frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$$

*References:*
- [A364175](https://oeis.org/A364175)
-/
open Real Nat Int

namespace OeisA364175

/--
The sequence $a(n) = \frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$ for $n$ divisible by 3.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  dsimp only [a]
  simp only [Nat.cast_zero, mul_zero, zero_add, Real.Gamma_one, mul_one,
    div_self (one_ne_zero : (1 : ℝ) ≠ 0), round_one, Int.toNat_one]

@[category test, AMS 11]
theorem a_1 : a 1 = 36 := by
  have h_val :
      (Real.Gamma (6 * (1:ℝ) + 1) * Real.Gamma (2 / 3 * (1:ℝ) + 1)) /
        (Real.Gamma (3 * (1:ℝ) + 1) * Real.Gamma (2 * (1:ℝ) + 1) *
         Real.Gamma (5 / 3 * (1:ℝ) + 1)) =
        36 := by
    have h_eq :
        (Real.Gamma (6 * (1 : ℝ) + 1) * Real.Gamma (2 / 3 * (1 : ℝ) + 1)) /
          (Real.Gamma (3 * (1 : ℝ) + 1) * Real.Gamma (2 * (1 : ℝ) + 1) *
           Real.Gamma (5 / 3 * (1 : ℝ) + 1)) =
        (Real.Gamma 7 * Real.Gamma (5/3)) / (Real.Gamma 4 * Real.Gamma 3 * Real.Gamma (8/3)) := by
      congr 2 <;> congr 1 <;> congr 1 <;> norm_num
    rw [h_eq]
    have h1 : Real.Gamma (8/3) = (5/3) * Real.Gamma (5/3) := by
      have r1 : (8/3 : ℝ) = 5/3 + 1 := by norm_num
      rw [r1, Real.Gamma_add_one (by norm_num)]
    rw [h1]
    have h_int_7 : Real.Gamma 7 = 720 := by norm_num
    have h_int_4 : Real.Gamma 4 = 6 := by norm_num
    have h_int_3 : Real.Gamma 3 = 2 := by norm_num
    rw [h_int_7, h_int_4, h_int_3]
    have hG : Real.Gamma (5/3) ≠ 0 := ne_of_gt (by positivity)
    have Hnum : 720 * Real.Gamma (5/3) = 720 * Real.Gamma (5/3) := by ring
    have Hden : 6 * 2 * (5/3 * Real.Gamma (5/3)) = (20 : ℝ) * Real.Gamma (5/3) := by ring
    rw [Hnum, Hden]
    rw [mul_div_mul_right _ _ hG]
    norm_num
  unfold a
  dsimp
  push_cast
  rw [h_val]
  norm_num
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3564 := by
  have h_val :
      (Real.Gamma (6 * (2:ℝ) + 1) * Real.Gamma (2 / 3 * (2:ℝ) + 1)) /
        (Real.Gamma (3 * (2:ℝ) + 1) * Real.Gamma (2 * (2:ℝ) + 1) *
         Real.Gamma (5 / 3 * (2:ℝ) + 1)) =
        3564 := by
    have h_eq :
        (Real.Gamma (6 * (2 : ℝ) + 1) * Real.Gamma (2 / 3 * (2 : ℝ) + 1)) /
          (Real.Gamma (3 * (2 : ℝ) + 1) * Real.Gamma (2 * (2 : ℝ) + 1) *
           Real.Gamma (5 / 3 * (2 : ℝ) + 1)) =
        (Real.Gamma 13 * Real.Gamma (7/3)) / (Real.Gamma 7 * Real.Gamma 5 * Real.Gamma (13/3)) := by
      congr 2 <;> congr 1 <;> congr 1 <;> norm_num
    rw [h_eq]
    have h1 : Real.Gamma (13/3) = (10/3) * (7/3) * Real.Gamma (7/3) := by
      have r1 : (13/3 : ℝ) = 10/3 + 1 := by norm_num
      have r2 : (10/3 : ℝ) = 7/3 + 1 := by norm_num
      rw [r1, Real.Gamma_add_one (by norm_num), r2, Real.Gamma_add_one (by norm_num)]
      ring
    rw [h1]
    have h_int_13 : Real.Gamma 13 = 479001600 := by norm_num
    have h_int_7 : Real.Gamma 7 = 720 := by norm_num
    have h_int_5 : Real.Gamma 5 = 24 := by norm_num
    rw [h_int_13, h_int_7, h_int_5]
    have hG : Real.Gamma (7/3) ≠ 0 := ne_of_gt (by positivity)
    have Hnum : 479001600 * Real.Gamma (7/3) = 479001600 * Real.Gamma (7/3) := by ring
    have Hden : 720 * 24 * (10/3 * (7/3) * Real.Gamma (7/3)) = (134400 : ℝ) * Real.Gamma (7/3) :=
      by ring
    rw [Hnum, Hden]
    rw [mul_div_mul_right _ _ hG]
    norm_num
  unfold a
  dsimp
  rw [h_val]
  norm_num
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 408408 := by
  have h_val :
      (Real.Gamma (6 * (3:ℝ) + 1) * Real.Gamma (2 / 3 * (3:ℝ) + 1)) /
        (Real.Gamma (3 * (3:ℝ) + 1) * Real.Gamma (2 * (3:ℝ) + 1) *
         Real.Gamma (5 / 3 * (3:ℝ) + 1)) =
        408408 := by
    have h_eq :
        (Real.Gamma (6 * (3 : ℝ) + 1) * Real.Gamma (2 / 3 * (3 : ℝ) + 1)) /
          (Real.Gamma (3 * (3 : ℝ) + 1) * Real.Gamma (2 * (3 : ℝ) + 1) *
           Real.Gamma (5 / 3 * (3 : ℝ) + 1)) =
        (Real.Gamma 19 * Real.Gamma 3) / (Real.Gamma 10 * Real.Gamma 7 * Real.Gamma 6) := by
      congr 2 <;> congr 1 <;> congr 1 <;> norm_num
    rw [h_eq]
    have h_int_19 : Real.Gamma 19 = 6402373705728000 := by norm_num
    have h_int_3 : Real.Gamma 3 = 2 := by norm_num
    have h_int_10 : Real.Gamma 10 = 362880 := by norm_num
    have h_int_7 : Real.Gamma 7 = 720 := by norm_num
    have h_int_6 : Real.Gamma 6 = 120 := by norm_num
    rw [h_int_19, h_int_3, h_int_10, h_int_7, h_int_6]
    norm_num
  unfold a
  dsimp
  rw [h_val]
  norm_num
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 49697388 := by
  have h_val :
      (Real.Gamma (6 * (4:ℝ) + 1) * Real.Gamma (2 / 3 * (4:ℝ) + 1)) /
        (Real.Gamma (3 * (4:ℝ) + 1) * Real.Gamma (2 * (4:ℝ) + 1) *
         Real.Gamma (5 / 3 * (4:ℝ) + 1)) =
        49697388 := by
    have h_eq :
        (Real.Gamma (6 * (4 : ℝ) + 1) * Real.Gamma (2 / 3 * (4 : ℝ) + 1)) /
          (Real.Gamma (3 * (4 : ℝ) + 1) * Real.Gamma (2 * (4 : ℝ) + 1) *
           Real.Gamma (5 / 3 * (4 : ℝ) + 1)) =
        (Real.Gamma 25 * Real.Gamma (11/3)) /
          (Real.Gamma 13 * Real.Gamma 9 * Real.Gamma (23/3)) := by
      congr 2 <;> congr 1 <;> congr 1 <;> norm_num
    rw [h_eq]
    have h1 : Real.Gamma (23/3) = (20/3) * (17/3) * (14/3) * (11/3) * Real.Gamma (11/3) := by
      have r1 : (23/3 : ℝ) = 20/3 + 1 := by norm_num
      have r2 : (20/3 : ℝ) = 17/3 + 1 := by norm_num
      have r3 : (17/3 : ℝ) = 14/3 + 1 := by norm_num
      have r4 : (14/3 : ℝ) = 11/3 + 1 := by norm_num
      rw [r1, Real.Gamma_add_one (by norm_num)]
      rw [r2, Real.Gamma_add_one (by norm_num)]
      rw [r3, Real.Gamma_add_one (by norm_num)]
      rw [r4, Real.Gamma_add_one (by norm_num)]
      ring
    rw [h1]
    have h_int_25 : Real.Gamma 25 = 620448401733239439360000 := by norm_num
    have h_int_13 : Real.Gamma 13 = 479001600 := by norm_num
    have h_int_9 : Real.Gamma 9 = 40320 := by norm_num
    rw [h_int_25, h_int_13, h_int_9]
    have hG : Real.Gamma (11/3) ≠ 0 := ne_of_gt (by positivity)
    have Hden :
      479001600 * 40320 * ((20 / 3) * (17 / 3) * (14 / 3) * (11 / 3) * Real.Gamma (11/3)) =
        (479001600 * 40320 * (20 / 3) * (17 / 3) * (14 / 3) * (11 / 3) : ℝ) * Real.Gamma (11/3) :=
      by ring
    rw [Hden]
    rw [mul_div_mul_right _ _ hG]
    norm_num
  unfold a
  dsimp
  rw [h_val]
  norm_num
  rfl

/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $r$.
Note: The expression $r-1$ is a natural number subtraction, which is safe since $r$ is positive.
-/
@[category research open, AMS 11]
theorem supercongruence (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OeisA364175
