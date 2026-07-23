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

/--
Number of ordered ways to write $n$ as $w^2 + x^3 + 2y^3 + 3z^3$, where $w, x, y$ and $z$ are nonnegative integers.
$$a(n) = \#\left\{(w, x, y, z) \in \mathbb{N}^4 \mid n = w^2 + x^3 + 2y^3 + 3z^3\right\}$$
-/
def A262824 (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum fun w =>
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then 1 else 0


theorem a_zero : A262824 0 = 1 := by
  trivial

theorem a_one : A262824 1 = 2 := by
  sorry

theorem a_two : A262824 2 = 2 := by
  sorry

theorem a_three : A262824 3 = 3 := by
  sorry

/--
Conjecture (i): For any m = 3, 4, 5, 6 and n >= 0, there are nonnegative integers w, x, y, z such that
n = w^2 + x^3 + 2*y^3 + m*z^3.
Conjecture (ii): For P(w,x,y,z) = w^2 + x^3 + 2*y^3 + z^4, w^2 + x^3 + 2*y^3 + 3*z^4, w^2 + x^3 + 2*y^3 + 6*z^4,
2*w^2 + x^3 + 4*y^3 + z^4, we have {P(w,x,y,z): w,x,y,z = 0,1,2,...} ={0,1,2,...}.
-/
theorem oeis_262824_conjecture_i_and_ii :
  -- Part (i)
  (
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 5 * z ^ 3) ∧
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 6 * z ^ 3)
  ) ∧
  -- Part (ii)
  (
    -- P_1: w^2 + x^3 + 2*y^3 + z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + z ^ 4) ∧
    -- P_2: w^2 + x^3 + 2*y^3 + 3*z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4) ∧
    -- P_3: w^2 + x^3 + 2*y^3 + 6*z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 6 * z ^ 4) ∧
    -- P_4: 2*w^2 + x^3 + 4*y^3 + z^4
    (∀ n : Nat, ∃ w x y z : Nat, n = 2 * w ^ 2 + x ^ 3 + 4 * y ^ 3 + z ^ 4)
  ) := by sorry
