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
import Mathlib.Data.Nat.Prime.Nth

/-!
# Conjectures associated with A110854

$a(n) = \mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$,
where $\mathrm{prime}(k)$ is the $k$-th prime number.

*References:*
- [A110854](https://oeis.org/A110854)
-/

namespace OeisA110854

open Nat

/--
The primary defining sequence `a`.
$a(n)$ is $\mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let p (k : ℕ) : ℤ := (Nat.nth Nat.Prime (k - 1)).cast
  if n = 0 then 0
  else p (2 * n + 2) - p (2 * n + 1) - p (2 * n) + p (2 * n - 1)

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  rw [nth_prime_five, Nat.nth_prime_four_eq_eleven, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_two_eq_five]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  rw [nth_prime_seven, nth_prime_six, nth_prime_five, Nat.nth_prime_four_eq_eleven]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  dsimp [a]
  rw [nth_prime_nine, nth_prime_eight, nth_prime_seven, nth_prime_six]
  norm_num

/--
Do the absolute values cover A004275?
A004275 is the set of all differences between two prime numbers.
The conjecture asks whether every possible difference between two prime numbers
occurs as the absolute value of some term $a(n)$.
-/
@[category research open, AMS 11]
theorem conjecture :
  ∀ d > 0, (∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ d = (p1 - p2 : ℤ).natAbs) →
  ∃ n > 0, d = (a n).natAbs := by
  sorry

end OeisA110854
