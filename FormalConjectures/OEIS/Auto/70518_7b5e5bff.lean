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

open Polynomial

/--
A070518: Value of $n$-th cyclotomic polynomial at $n$.
$$ a(n) = \Phi_n(n) $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Polynomial.eval (Int.ofNat n) (cyclotomic n ℤ)).natAbs


theorem a_one : a 1 = 0 := by
  delta a
  norm_num

theorem a_two : a 2 = 3 := by
  (inhabit Int)
  norm_num[a]

theorem a_three : a 3 = 13 := by
  symm
  simp_all[a]

theorem a_four : a 4 = 17 := by
  delta a
  have α := (Polynomial.prod_cyclotomic_eq_X_pow_sub_one four_pos Int)
  simp_all[(by decide:(4).divisors={1,2,4}),Int.natAbs_eq_iff]
  exact (.inl (mul_left_cancel₀ (by decide: (3:ℤ) * (5)≠0) (by linear_combination2(norm:=norm_num[←mul_assoc])congr_arg (Polynomial.eval @4) α)))

/--
A070518 a(28341) is divisible by 283411^2. What is the next n such that a(n) is not squarefree? - _Jianing Song_, Nov 01 2024
-/
theorem oeis_70518_conjecture_0 :
  (283411 : ℕ) ^ 2 ∣ a 28341 :=
by sorry
