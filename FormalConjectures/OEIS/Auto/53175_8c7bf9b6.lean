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

open Nat

/--
A053175: Catalan-Larcombe-French sequence, defined by the recurrence relation:
$$a(n) n^2 = a(n-1) \cdot 8(3n^2 - 3n + 1) - a(n-2) \cdot 128(n-1)^2$$
with $a(0)=1$ and $a(1)=8$.
The result is the integer quotient, which is exact.
-/
def a : ℕ → ℕ
| 0 => 1
| 1 => 8
| n + 2 => -- compute a(n') where n' = n + 2
  let n' := n + 2
  let an_minus_1 := a (n + 1)
  let an_minus_2 := a n

  let term1_factor := 8 * (3 * n'^2 - 3 * n' + 1)
  let term2_factor := 128 * (n' - 1)^2

  -- The subtraction is safe because these are known positive integers, and the left side is larger.
  (term1_factor * an_minus_1 - term2_factor * an_minus_2) / (n'^2)

theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 8 := by
  rfl

theorem a_two : a 2 = 80 := by
  rfl

theorem a_three : a 3 = 896 := by
  rfl

open Matrix

def a_z (n : ℕ) : ℤ := a n

/--
P(n) is the (n+1) x (n+1) Hankel-type matrix whose (i,j)-entry is a(i+j) for all i,j = 0,...,n.
The matrix indices are `Fin (n + 1)`.
-/
def P (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  of fun i j : Fin (n + 1) => a_z (i.val + j.val)

/--
Conjecture: Let P(n) be the (n+1) X (n+1) Hankel-type determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,n.
Then P(n)/2^(n*(n+3)) is a positive odd integer. - Zhi-Wei Sun, Aug 14 2013
-/
theorem oeis_53175_conjecture_0 (n : ℕ) :
  let det_P_n := (P n).det
  let exponent := n * (n + 3)
  let power_of_2 := (2 : ℤ) ^ exponent
  -- Hairy division: $\det(P(n))$ must be divisible by $2^{n(n+3)}$.
  power_of_2 ∣ det_P_n ∧
  -- The quotient is a positive odd integer.
  ((det_P_n / power_of_2) > 0 ∧ ((det_P_n / power_of_2) % 2 = 1)) :=
by sorry
