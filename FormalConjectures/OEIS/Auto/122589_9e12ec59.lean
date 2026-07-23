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

open Int

/--
A122589: Expansion of $1/(1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6)$.
The sequence is defined by the linear recurrence relation:
$a(n) = 11 a(n-1) - 45 a(n-2) + 84 a(n-3) - 70 a(n-4) + 21 a(n-5) - a(n-6)$ for $n \ge 6$.
The initial values are $a(0)=1, a(1)=11, a(2)=76, a(3)=425, a(4)=2109, a(5)=9709$.
-/
def a (n : ℕ) : ℕ :=
  let rec a_int : ℕ → ℤ := fun n =>
    match n with
    | 0 => 1
    | 1 => 11
    | 2 => 76
    | 3 => 425
    | 4 => 2109
    | 5 => 9709
    | k + 6 =>
      11 * a_int (k + 5)
      - 45 * a_int (k + 4)
      + 84 * a_int (k + 3)
      - 70 * a_int (k + 2)
      + 21 * a_int (k + 1)
      - a_int k
  (a_int n).toNat


theorem a_zero : a 0 = 1 := by
  constructor

theorem a_one : a 1 = 11 := by
  classical constructor

theorem a_two : a 2 = 76 := by
  (rfl )

theorem a_three : a 3 = 425 := by
  symm
  show 425= (a 3)
  rfl

open Polynomial

/--
The conjecture suggested by the study of polynomials associated with the regular 13-gon
is that the denominator of the generating function for A122589 factors based on
the cosines of the angles of a regular 13-gon.
Specifically, let $P(x)$ be the denominator of the generating function. Then
$$P(x) = 1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6 = \prod_{k=1}^6 \left(1 - 4 \cos^2\left(\frac{\pi k}{13}\right) x\right)$$
-/
theorem oeis_a122589_conjecture_0 :
    (C (1 : ℝ) - C (11 : ℝ) * X + C (45 : ℝ) * X^2 - C (84 : ℝ) * X^3 + C (70 : ℝ) * X^4 - C (21 : ℝ) * X^5 + C (1 : ℝ) * X^6)
    = Finset.prod (Finset.range 6)
        (fun k : ℕ => C (1 : ℝ) - C (4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2) * X) := by
  sorry

instance : Coe ℕ ℝ where
  coe := Nat.cast
