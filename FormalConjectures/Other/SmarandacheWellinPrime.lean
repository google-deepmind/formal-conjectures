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
# Smarandache–Wellin primes

The Smarandache–Wellin numbers are formed by concatenating the decimal expansions of the
successive primes: $2, 23, 235, 2357, \ldots$. It is conjectured that infinitely many members of
this sequence are prime.

*References:*
* [Smarandache Problems](https://fs.unm.edu/S-PROBL.HTM)
* [OEIS A019518](https://oeis.org/A019518)
* [OEIS A069151](https://oeis.org/A069151)
* [OEIS A046035](https://oeis.org/A046035)
-/

namespace SmarandacheWellinPrime

/-- The number of decimal digits of a natural number, counting zero as one digit. -/
def decimalDigitCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 10 n).length

/-- Append the decimal expansion of `right` to that of `left`. -/
def decimalAppend (left right : ℕ) : ℕ :=
  left * 10 ^ decimalDigitCount right + right

/-- The Smarandache–Wellin sequence, indexed from zero. -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => decimalAppend (a n) ((n + 1).nth Nat.Prime)

@[category API, AMS 11]
theorem nth_prime_one : (1).nth Nat.Prime = 3 :=
  Nat.nth_count Nat.prime_three

@[category API, AMS 11]
theorem nth_prime_two : (2).nth Nat.Prime = 5 :=
  Nat.nth_count Nat.prime_five

@[category API, AMS 11]
theorem nth_prime_three : (3).nth Nat.Prime = 7 :=
  Nat.nth_count Nat.prime_seven

@[category API, AMS 11]
theorem nth_prime_four : (4).nth Nat.Prime = 11 :=
  Nat.nth_count Nat.prime_eleven

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 23 := by
  norm_num [a, nth_prime_one, decimalAppend, decimalDigitCount]

@[category test, AMS 11]
theorem a_2 : a 2 = 235 := by
  norm_num [a, nth_prime_one, nth_prime_two, decimalAppend, decimalDigitCount]

@[category test, AMS 11]
theorem a_3 : a 3 = 2357 := by
  norm_num [a, nth_prime_one, nth_prime_two, nth_prime_three, decimalAppend, decimalDigitCount]

@[category test, AMS 11]
theorem a_4 : a 4 = 235711 := by
  norm_num [a, nth_prime_one, nth_prime_two, nth_prime_three, nth_prime_four, decimalAppend,
    decimalDigitCount]

@[category test, AMS 11]
theorem prime_a_0 : (a 0).Prime := by
  rw [a_0]
  norm_num

@[category test, AMS 11]
theorem prime_a_1 : (a 1).Prime := by
  rw [a_1]
  norm_num

@[category test, AMS 11]
theorem not_prime_a_2 : ¬ (a 2).Prime := by
  rw [a_2]
  norm_num

@[category test, AMS 11]
theorem prime_a_3 : (a 3).Prime := by
  rw [a_3]
  norm_num

@[category test, AMS 11]
theorem not_prime_a_4 : ¬ (a 4).Prime := by
  rw [a_4]
  norm_num

/-- [Smarandache Problems](https://fs.unm.edu/S-PROBL.HTM) states: "There are infinitely many
primes in the smarandache concatenated prime sequence." -/
@[category research open, AMS 11]
theorem conjecture : {n : ℕ | (a n).Prime}.Infinite := by
  sorry

end SmarandacheWellinPrime
