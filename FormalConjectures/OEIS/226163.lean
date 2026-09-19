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
# Determinant of Legendre symbol matrix with factorial shifts

Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! j}{p_n}\right),$$
where $p_n$ is the $n$-th prime ($n \ge 2$).

*References:*
- [A226163](https://oeis.org/A226163)
-/

namespace OeisA226163

open Matrix

/-- The $(p-1)/2$-by-$(p-1)/2$ matrix with $(i,j)$-entry being the Jacobi symbol
$\left(\frac{i^2 - \left(\frac{p-1}{2}\right)! j}{p}\right)$ for $1 \le i, j \le (p-1)/2$. -/
def legendreMatrix (p : ℕ) : Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) ℤ :=
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial
  fun i j =>
    let i' : ℤ := i.val + 1
    let j' : ℤ := j.val + 1
    jacobiSym (i' * i' - C * j') p

/-- Determinant of `legendreMatrix` for the $n$-th prime $p_n$. -/
noncomputable def a (n : ℕ) : ℤ :=
  (legendreMatrix (Nat.nth Nat.Prime (n - 1))).det

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h : Nat.nth Nat.Prime (1 - 1) = 2 := Nat.nth_prime_zero_eq_two
  rw [a, h]
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  have h : Nat.nth Nat.Prime (2 - 1) = 3 := Nat.nth_prime_one_eq_three
  rw [a, h]
  native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by
  have h : Nat.nth Nat.Prime (3 - 1) = 5 := Nat.nth_prime_two_eq_five
  rw [a, h]
  native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  have h : Nat.nth Nat.Prime (4 - 1) = 7 := Nat.nth_prime_three_eq_seven
  rw [a, h]
  native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  have h : Nat.nth Nat.Prime (5 - 1) = 11 := Nat.nth_prime_four_eq_eleven
  rw [a, h]
  native_decide

@[category test, AMS 11]
theorem a_6 : a 6 = -8 := by
  have h : Nat.nth Nat.Prime (6 - 1) = 13 := Nat.nth_count (show (13).Prime by decide)
  rw [a, h]
  native_decide

/--
Conjecture: $a(n) = 0$ if and only if $p_n \equiv 3 \pmod 4$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 2 ≤ n) :
    a n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  sorry

end OeisA226163
