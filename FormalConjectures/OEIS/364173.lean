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
# Factorial ratio $\frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$

The sequence is defined for even $n = 2m$ by
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$

*References:*
- [A364173](https://oeis.org/A364173)
-/
open scoped Real

namespace OeisA364173

/--
The sequence $a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$ for even $n$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) *
   Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_1 : a 1 = 128 := by
  have h_eq :
      a 1 = (Real.Gamma 10 * Real.Gamma 3 * Real.Gamma (5/2)) /
        (Real.Gamma (11/2) * Real.Gamma 5 * Real.Gamma 4 * Real.Gamma 2) := by
    unfold a; dsimp; congr 2 <;> congr 1 <;> congr 1 <;> norm_num
  rw [h_eq]
  have h1 : Real.Gamma (11/2) = (9/2) * (7/2) * (5/2) * Real.Gamma (5/2) := by
    have r1 : (11/2 : ℝ) = 9/2 + 1 := by norm_num
    have r2 : (9/2 : ℝ) = 7/2 + 1 := by norm_num
    have r3 : (7/2 : ℝ) = 5/2 + 1 := by norm_num
    rw [r1, Real.Gamma_add_one (by norm_num)]
    rw [r2, Real.Gamma_add_one (by norm_num)]
    rw [r3, Real.Gamma_add_one (by norm_num)]
    ring
  rw [h1]
  have h_int_10 : Real.Gamma 10 = 362880 := by norm_num
  have h_int_3 : Real.Gamma 3 = 2 := by norm_num
  have h_int_5 : Real.Gamma 5 = 24 := by norm_num
  have h_int_4 : Real.Gamma 4 = 6 := by norm_num
  have h_int_2 : Real.Gamma 2 = 1 := by norm_num
  rw [h_int_10, h_int_3, h_int_5, h_int_4, h_int_2]
  have hG : Real.Gamma (5/2) ≠ 0 := ne_of_gt (by positivity)
  have Hnum : 362880 * 2 * Real.Gamma (5/2) = 725760 * Real.Gamma (5/2) := by ring
  have Hden :
      (9/2 * (7/2) * (5/2) * Real.Gamma (5/2) * 24 * 6 * 1) = (5670 : ℝ) * Real.Gamma (5/2) :=
    by ring
  rw [Hnum, Hden]
  rw [mul_div_mul_right _ _ hG]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 43758 := by
  have h_eq :
      a 2 = (Real.Gamma 19 * Real.Gamma 5 * Real.Gamma 4) /
        (Real.Gamma 10 * Real.Gamma 9 * Real.Gamma 7 * Real.Gamma 3) := by
    unfold a; dsimp; congr 2 <;> congr 1 <;> congr 1 <;> norm_num
  rw [h_eq]
  have h_int_19 : Real.Gamma 19 = 6402373705728000 := by norm_num
  have h_int_10 : Real.Gamma 10 = 362880 := by norm_num
  have h_int_9 : Real.Gamma 9 = 40320 := by norm_num
  have h_int_7 : Real.Gamma 7 = 720 := by norm_num
  have h_int_5 : Real.Gamma 5 = 24 := by norm_num
  have h_int_4 : Real.Gamma 4 = 6 := by norm_num
  have h_int_3 : Real.Gamma 3 = 2 := by norm_num
  rw [h_int_19, h_int_10, h_int_9, h_int_7, h_int_5, h_int_4, h_int_3]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 17039360 := by
  have h_eq :
      a 3 = (Real.Gamma 28 * Real.Gamma 7 * Real.Gamma (11/2)) /
        (Real.Gamma (29/2) * Real.Gamma 13 * Real.Gamma 10 * Real.Gamma 4) := by
    unfold a; dsimp; congr 2 <;> congr 1 <;> congr 1 <;> norm_num
  rw [h_eq]
  have h1 :
      Real.Gamma (29/2) =
        (27/2) * (25/2) * (23/2) * (21/2) * (19/2) * (17/2) * (15/2) * (13/2) * (11/2) *
        Real.Gamma (11/2) := by
    have r1 : (29/2 : ℝ) = 27/2 + 1 := by norm_num
    have r2 : (27/2 : ℝ) = 25/2 + 1 := by norm_num
    have r3 : (25/2 : ℝ) = 23/2 + 1 := by norm_num
    have r4 : (23/2 : ℝ) = 21/2 + 1 := by norm_num
    have r5 : (21/2 : ℝ) = 19/2 + 1 := by norm_num
    have r6 : (19/2 : ℝ) = 17/2 + 1 := by norm_num
    have r7 : (17/2 : ℝ) = 15/2 + 1 := by norm_num
    have r8 : (15/2 : ℝ) = 13/2 + 1 := by norm_num
    have r9 : (13/2 : ℝ) = 11/2 + 1 := by norm_num
    rw [r1, Real.Gamma_add_one (by norm_num)]
    rw [r2, Real.Gamma_add_one (by norm_num)]
    rw [r3, Real.Gamma_add_one (by norm_num)]
    rw [r4, Real.Gamma_add_one (by norm_num)]
    rw [r5, Real.Gamma_add_one (by norm_num)]
    rw [r6, Real.Gamma_add_one (by norm_num)]
    rw [r7, Real.Gamma_add_one (by norm_num)]
    rw [r8, Real.Gamma_add_one (by norm_num)]
    rw [r9, Real.Gamma_add_one (by norm_num)]
    ring
  rw [h1]
  have h_int_28 : Real.Gamma 28 = 10888869450418352160768000000 := by norm_num
  have h_int_7 : Real.Gamma 7 = 720 := by norm_num
  have h_int_13 : Real.Gamma 13 = 479001600 := by norm_num
  have h_int_10 : Real.Gamma 10 = 362880 := by norm_num
  have h_int_4 : Real.Gamma 4 = 6 := by norm_num
  rw [h_int_28, h_int_7, h_int_13, h_int_10, h_int_4]
  have hG : Real.Gamma (11/2) ≠ 0 := ne_of_gt (by positivity)
  have Hnum : 10888869450418352160768000000 * 720 * Real.Gamma (11/2) =
      7839986004301213555752960000000 * Real.Gamma (11/2) :=
    by ring
  have Hden : ((27/2) * (25/2) * (23/2) * (21/2) * (19/2) * (17/2) * (15/2) * (13/2) * (11/2) *
      Real.Gamma (11/2) * 479001600 * 362880 * 6) =
      (460110356509940136000000 : ℝ) * Real.Gamma (11/2) :=
    by ring
  rw [Hnum, Hden]
  rw [mul_div_mul_right _ _ hG]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 7012604550 := by
  unfold a
  norm_num

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
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by sorry

end OeisA364173
