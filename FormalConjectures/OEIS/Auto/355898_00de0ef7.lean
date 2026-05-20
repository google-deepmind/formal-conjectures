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
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2))}$.
-/
def A355898 : ℕ → ℕ
| 0 => 0 -- Sequence starts properly at A355898(1)
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

theorem a_one : A355898 1 = 1 := by
  rfl

theorem a_two : A355898 2 = 1 := by
  rfl

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) :=
by sorry
