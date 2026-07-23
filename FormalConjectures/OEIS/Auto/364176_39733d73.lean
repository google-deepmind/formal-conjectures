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

open Real Nat

/--
A364176 term:
$$a(n) = \frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$$
where integer factorials are evaluated using `Nat.factorial`, and fractional factorials $x!$ are defined as $\Gamma(x+1)$.
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


theorem a_zero : a 0 = 1 := by
  norm_num[a]

theorem a_one : a 1 = 7168 := by
  simp_all[a]
  push_cast[mul_assoc,·!]
  use div_eq_of_eq_mul (by positivity)<|symm (.trans (by rw [ Real.Gamma_add_one (by norm_num)]) ? _)
  linarith [ ((7/2):ℝ).Gamma_add_one (by simp_all), (5/2+2:ℝ).Gamma_add_one (by norm_num), (5/2+3:ℝ).Gamma_add_one (by·norm_num), (5/2+4:Real).Gamma_add_one (by norm_num)]

theorem a_two : a 2 = 168043980 := by
  delta a
  classical norm_num

theorem a_three : a 3 = 4488240824320 := by
  delta a
  norm_num only[·!]
  use(div_eq_iff<|by positivity).2<|symm <|.trans (by rw [show (47/2:ℝ)=17/2+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1by ring,Real.Gamma_add_one (by bound)]) ?_
  repeat rw[Real.Gamma_add_one (by bound)]
  ring

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: The sequence a(n) is only conjecturally integer-valued. We formalize the congruence as divisibility of real numbers, requiring that the sequence terms are indeed integers.
-/
theorem oeis_364176_conjecture_0
  (p : ℕ) (hp : Nat.Prime p) (hp_ge_five : 5 ≤ p)
  (n r : ℕ) (hn_pos : 0 < n) (hr_pos : 0 < r) :
  -- Define the arguments for a, ensuring r-1 is safe (guaranteed by hr_pos)
  let k_r := n * p ^ r
  let k_r_minus_1 := n * p ^ (r - 1)
  -- Define the modulus as a real number
  let modulus : ℝ := (p ^ (3 * r)).cast
  -- The premise is the conjectural integrality of the two relevant terms, i.e., they are in the image of Int.cast
  (a k_r ∈ Set.range (Int.cast : ℤ → ℝ)) ∧ (a k_r_minus_1 ∈ Set.range (Int.cast : ℤ → ℝ)) →
  -- The conclusion is the divisibility condition: modulus divides the difference.
  -- This is formalized as the quotient being an integer.
  (a k_r - a k_r_minus_1) / modulus ∈ Set.range (Int.cast : ℤ → ℝ)
:= by sorry
