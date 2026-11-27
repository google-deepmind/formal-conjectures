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
# Factorial ratio $\frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$

The sequence is defined for even $n = 2m$ by
$$a(n) = \frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$$

*References:*
- [A364176](https://oeis.org/A364176)
-/
open Real Nat

namespace OeisA364176

/--
The sequence $a(n) = \frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$ for even $n$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n.cast
  let num_int_15 : ℝ := (15 * n).factorial.cast
  let num_int_2 : ℝ := (2 * n).factorial.cast
  let num_frac_5_halves : ℝ := Real.Gamma (5 * n_r / 2 + 1)

  let den_frac_15_halves : ℝ := Real.Gamma (15 * n_r / 2 + 1)
  let den_int_6 : ℝ := (6 * n).factorial.cast
  let den_int_5 : ℝ := (5 * n).factorial.cast
  let den_int_1 : ℝ := n.factorial.cast

  (num_int_15 * num_frac_5_halves * num_int_2) /
  (den_frac_15_halves * den_int_6 * den_int_5 * den_int_1)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  norm_num[a]

@[category test, AMS 11]
theorem a_1 : a 1 = 7168 := by
  unfold a
  have h_eq :
      ( (((15 * 1:ℕ).factorial : ℝ) * Real.Gamma (5 * (1:ℕ) / 2 + 1) * ((2 * 1:ℕ).factorial : ℝ)) /
        (Real.Gamma (15 * (1:ℕ) / 2 + 1) * ((6 * 1:ℕ).factorial : ℝ) * ((5 * 1:ℕ).factorial : ℝ) *
         ((1:ℕ).factorial : ℝ)) ) = 7168 := by
    push_cast
    have h_num_gamma : Real.Gamma (5 * (1:ℝ) / 2 + 1) = Real.Gamma (7/2) := by norm_num
    have h_den_gamma : Real.Gamma (15 * (1:ℝ) / 2 + 1) = Real.Gamma (17/2) := by norm_num
    rw [h_num_gamma, h_den_gamma]
    have h1 : Real.Gamma (17/2) = 15/2 * 13/2 * 11/2 * 9/2 * 7/2 * Real.Gamma (7/2) := by
      have r1 : (17/2 : ℝ) = 15/2 + 1 := by norm_num
      have r2 : (15/2 : ℝ) = 13/2 + 1 := by norm_num
      have r3 : (13/2 : ℝ) = 11/2 + 1 := by norm_num
      have r4 : (11/2 : ℝ) = 9/2 + 1 := by norm_num
      have r5 : (9/2 : ℝ) = 7/2 + 1 := by norm_num
      rw [r1, Real.Gamma_add_one (by norm_num), r2, Real.Gamma_add_one (by norm_num), r3,
          Real.Gamma_add_one (by norm_num), r4, Real.Gamma_add_one (by norm_num), r5,
          Real.Gamma_add_one (by norm_num)]
      ring

    have hG : Real.Gamma (7/2) ≠ 0 := ne_of_gt (by positivity)
    have Hden_sub : (15/2 * 13/2 * 11/2 * 9/2 * 7/2) = (135135/32 : ℝ) := by norm_num
    have h_eval :
        (1307674368000 * Real.Gamma (7/2) * 2) /
        ((135135/32 * Real.Gamma (7/2)) * 720 * 120 * 1) = 7168 := by
      have Hnum : 1307674368000 * Real.Gamma (7/2) * 2 = (2615348736000 : ℝ) * Real.Gamma (7/2) :=
        by ring
      have Hden :
        ((135135/32) * Real.Gamma (7/2)) * 720 * 120 * 1 =
        ((135135/32 * 720 * 120 * 1) : ℝ) * Real.Gamma (7/2) :=
        by ring
      rw [Hnum, Hden]
      rw [mul_div_mul_right _ _ hG]
      norm_num
    have hf15 : (((15 : ℕ).factorial : ℝ)) = 1307674368000 := by norm_num
    have hf2 : (((2 : ℕ).factorial : ℝ)) = 2 := by norm_num
    have hf6 : (((6 : ℕ).factorial : ℝ)) = 720 := by norm_num
    have hf5 : (((5 : ℕ).factorial : ℝ)) = 120 := by norm_num
    have hf1 : (((1 : ℕ).factorial : ℝ)) = 1 := by norm_num
    rw [h1]
    rw [Hden_sub]
    rw [hf15, hf2, hf6, hf5, hf1]
    exact h_eval
  exact h_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 168043980 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 4488240824320 := by
  unfold a
  have h_eq :
      ( (((15 * 3:ℕ).factorial : ℝ) * Real.Gamma (5 * (3:ℕ) / 2 + 1) * ((2 * 3:ℕ).factorial : ℝ)) /
        (Real.Gamma (15 * (3:ℕ) / 2 + 1) * ((6 * 3:ℕ).factorial : ℝ) * ((5 * 3:ℕ).factorial : ℝ) *
         ((3:ℕ).factorial : ℝ)) ) = 4488240824320 := by
    push_cast
    have h_num_gamma : Real.Gamma (5 * (3:ℝ) / 2 + 1) = Real.Gamma (17/2) := by norm_num
    have h_den_gamma : Real.Gamma (15 * (3:ℝ) / 2 + 1) = Real.Gamma (47/2) := by norm_num
    rw [h_num_gamma, h_den_gamma]
    have h1 :
        Real.Gamma (47/2) =
          45/2 * 43/2 * 41/2 * 39/2 * 37/2 * 35/2 * 33/2 * 31/2 * 29/2 * 27/2 * 25/2 * 23/2 *
          21/2 * 19/2 * 17/2 * Real.Gamma (17/2) := by
      have r1 : (47/2 : ℝ) = 45/2 + 1 := by norm_num
      have r2 : (45/2 : ℝ) = 43/2 + 1 := by norm_num
      have r3 : (43/2 : ℝ) = 41/2 + 1 := by norm_num
      have r4 : (41/2 : ℝ) = 39/2 + 1 := by norm_num
      have r5 : (39/2 : ℝ) = 37/2 + 1 := by norm_num
      have r6 : (37/2 : ℝ) = 35/2 + 1 := by norm_num
      have r7 : (35/2 : ℝ) = 33/2 + 1 := by norm_num
      have r8 : (33/2 : ℝ) = 31/2 + 1 := by norm_num
      have r9 : (31/2 : ℝ) = 29/2 + 1 := by norm_num
      have r10 : (29/2 : ℝ) = 27/2 + 1 := by norm_num
      have r11 : (27/2 : ℝ) = 25/2 + 1 := by norm_num
      have r12 : (25/2 : ℝ) = 23/2 + 1 := by norm_num
      have r13 : (23/2 : ℝ) = 21/2 + 1 := by norm_num
      have r14 : (21/2 : ℝ) = 19/2 + 1 := by norm_num
      have r15 : (19/2 : ℝ) = 17/2 + 1 := by norm_num
      rw [r1, Real.Gamma_add_one (by norm_num), r2, Real.Gamma_add_one (by norm_num), r3,
          Real.Gamma_add_one (by norm_num), r4, Real.Gamma_add_one (by norm_num), r5,
          Real.Gamma_add_one (by norm_num), r6, Real.Gamma_add_one (by norm_num), r7,
          Real.Gamma_add_one (by norm_num), r8, Real.Gamma_add_one (by norm_num), r9,
          Real.Gamma_add_one (by norm_num), r10, Real.Gamma_add_one (by norm_num), r11,
          Real.Gamma_add_one (by norm_num), r12, Real.Gamma_add_one (by norm_num), r13,
          Real.Gamma_add_one (by norm_num), r14, Real.Gamma_add_one (by norm_num), r15,
          Real.Gamma_add_one (by norm_num)]
      ring

    have hG : Real.Gamma (17/2) ≠ 0 := ne_of_gt (by positivity)
    have Hden_sub :
        (45/2 * 43/2 * 41/2 * 39/2 * 37/2 * 35/2 * 33/2 * 31/2 * 29/2 * 27/2 * 25/2 * 23/2 * 21/2 *
         19/2 * 17/2) = (12517749576658530579375/32768 : ℝ) :=
      by norm_num
    have h_eval :
        (119622220865480194561963161495657715064383733760000000000 * Real.Gamma (17/2) * 720) /
        ((12517749576658530579375/32768 * Real.Gamma (17/2)) * 6402373705728000 *
         1307674368000 * 6) =
        4488240824320 := by
      have Hnum :
        119622220865480194561963161495657715064383733760000000000 * Real.Gamma (17/2) * 720 =
          (86127999023145740084613476276873554846356288307200000000000 : ℝ) * Real.Gamma (17/2) :=
        by ring
      have Hden :
        ((12517749576658530579375/32768) * Real.Gamma (17/2)) * 6402373705728000 *
        1307674368000 * 6 =
          ((12517749576658530579375/32768 * 6402373705728000 * 1307674368000 * 6) : ℝ) *
          Real.Gamma (17/2) :=
        by ring
      rw [Hnum, Hden]
      rw [mul_div_mul_right _ _ hG]
      norm_num
    have hf15 : (((45 : ℕ).factorial : ℝ)) =
        119622220865480194561963161495657715064383733760000000000 :=
      by norm_num
    have hf2 : (((6 : ℕ).factorial : ℝ)) = 720 := by norm_num
    have hf6 : (((18 : ℕ).factorial : ℝ)) = 6402373705728000 := by norm_num
    have hf5 : (((15 : ℕ).factorial : ℝ)) = 1307674368000 := by norm_num
    have hf1 : (((3 : ℕ).factorial : ℝ)) = 6 := by norm_num
    rw [h1]
    rw [Hden_sub]
    rw [hf15, hf2, hf6, hf5, hf1]
    exact h_eval
  exact h_eq

@[category test, AMS 11]
theorem a_4 : a 4 = 126694219977836700 := by
  norm_num [a]

/--
Conjecture 1: This sequence is an integer sequence, i.e., $a(n) \in \mathbb{Z}$ for all $n$.
-/
@[category research open, AMS 11]
theorem conjecture_1_integrality : ∀ (n : ℕ), a n ∈ Set.range (Int.cast : ℤ → ℝ) := by
  sorry

/--
Conjecture 2: The supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$ hold for all
primes $p \ge 5$ and all positive integers $n$ and $r$.
-/
@[category research open, AMS 11]
theorem conjecture_2_supercongruence
  (p : ℕ) (hp : p.Prime) (hp_ge_five : 5 ≤ p)
  (n r : ℕ) (hn_pos : 0 < n) (hr_pos : 0 < r) :
  -- Define the arguments for a, ensuring r-1 is safe (guaranteed by hr_pos)
  let k_r := n * p ^ r
  let k_r_minus_1 := n * p ^ (r - 1)
  -- Define the modulus as a real number
  let modulus : ℝ := (p ^ (3 * r)).cast
  -- The premise is the conjectural integrality of the two relevant terms,
  -- i.e., they are in the image of Int.cast
  (a k_r ∈ Set.range (Int.cast : ℤ → ℝ)) ∧ (a k_r_minus_1 ∈ Set.range (Int.cast : ℤ → ℝ)) →
  -- The conclusion is the divisibility condition: modulus divides the difference.
  -- This is formalized as the quotient being an integer.
  (a k_r - a k_r_minus_1) / modulus ∈ Set.range (Int.cast : ℤ → ℝ)
:= by sorry

end OeisA364176
