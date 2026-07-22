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
# Sum of squares of nonacci numbers

Sum of squares of nonacci numbers (Fibonacci 9-step numbers).

*References:*
- [A107247](https://oeis.org/A107247)
-/

namespace OeisA107247

/-- Nonacci number (Fibonacci 9-step number).
$F_9(n)$ is defined by the linear recurrence $F_9(n+9) = \sum_{i=0}^8 F_9(n+i)$,
with $F_9(0) = \dots = F_9(7) = 0$ and $F_9(8) = 1$. -/
def nonacci : ℕ → ℕ
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 8 => 1
  | n + 9 =>
    nonacci (n + 8) + nonacci (n + 7) + nonacci (n + 6) + nonacci (n + 5) +
    nonacci (n + 4) + nonacci (n + 3) + nonacci (n + 2) + nonacci (n + 1) + nonacci n

/--
The primary defining sequence `a`.
`a n` is the sum of squares of nonacci numbers (Fibonacci 9-step numbers).
The official sequence matches the sum up to `n + 1` of the standard nonacci numbers to align with the offset.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 2)) fun k => (nonacci k) ^ 2

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

/--
A natural number is a semiprime if it is the product of exactly two primes (not necessarily distinct).
-/
def IsSemiprime (n : ℕ) : Prop :=
  1 < n ∧ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q

/--
Primes in this sequence include: a(8) = 2. Semiprimes in this sequence include: a(9) = 6 = 2 * 3, a(10) = 22 = 2 * 11, a(11) = 86 = 2 * 43, a(13) = 1366 = 2 * 683, a(14) = 5462 = 2 * 2731, a(16) = 87382 = 2 * 43691, a(17) = 348503 = 37 * 9419, a(27) = 358201316657 = 71 * 5045088967.
(Note: The OEIS comment uses 1-based indexing, so their indices are shifted by +1 compared to this formalization).
-/
@[category textbook, AMS 11]
theorem known_prime_and_semiprimes :
  Nat.Prime (a 8) ∧
  IsSemiprime (a 9) ∧
  IsSemiprime (a 10) ∧
  IsSemiprime (a 11) ∧
  IsSemiprime (a 13) ∧
  IsSemiprime (a 14) ∧
  IsSemiprime (a 16) ∧
  IsSemiprime (a 17) ∧
  IsSemiprime (a 27) := by
  sorry

/--
Primes in this sequence include: a(8) = 2, which is next?
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) = a (sInf {n : ℕ | 8 < n ∧ Nat.Prime (a n)}) := by
  sorry

end OeisA107247
