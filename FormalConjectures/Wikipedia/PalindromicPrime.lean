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

module

public import FormalConjecturesUtil

/-!
# Palindromic primes in base 10

A palindromic prime is a prime whose base-ten expansion reads the same in both directions. It is
unknown whether there are infinitely many such primes.

*References:*
* [Wikipedia, Palindromic prime](https://en.wikipedia.org/wiki/Palindromic_prime)
* [OEIS A002385](https://oeis.org/A002385)
-/

@[expose] public section

namespace PalindromicPrime

/-- Reverse the base-ten digits of a natural number. -/
def reverse10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- A palindromic prime is a prime fixed by base-ten digit reversal. -/
def IsPalindromicPrime (p : ℕ) : Prop :=
  p.Prime ∧ reverse10 p = p

@[category test, AMS 11]
theorem reverse10_101 : reverse10 101 = 101 := by
  norm_num [reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem reverse10_13 : reverse10 13 = 31 := by
  norm_num [reverse10, Nat.ofDigits]

/-- A trailing zero becomes a discarded leading zero after digit reversal. -/
@[category test, AMS 11]
theorem reverse10_120 : reverse10 120 = 21 := by
  norm_num [reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_2 : IsPalindromicPrime 2 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_11 : IsPalindromicPrime 11 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_101 : IsPalindromicPrime 101 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_131 : IsPalindromicPrime 131 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem a_151 : IsPalindromicPrime 151 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem not_a_13 : ¬ IsPalindromicPrime 13 := by
  norm_num [IsPalindromicPrime, reverse10, Nat.ofDigits]

@[category test, AMS 11]
theorem not_a_0 : ¬ IsPalindromicPrime 0 := by
  norm_num [IsPalindromicPrime]

@[category test, AMS 11]
theorem not_a_1 : ¬ IsPalindromicPrime 1 := by
  norm_num [IsPalindromicPrime]

/-- The palindrome $121 = 11^2$ is composite. -/
@[category test, AMS 11]
theorem not_a_121 : ¬ IsPalindromicPrime 121 := by
  norm_num [IsPalindromicPrime]

/-- [Wikipedia's article on palindromic primes](https://en.wikipedia.org/wiki/Palindromic_prime)
states: "It is not known if there are infinitely many palindromic primes in base 10." -/
@[category research open, AMS 11]
theorem infinitude_question :
    answer(sorry) ↔ {p : ℕ | IsPalindromicPrime p}.Infinite := by
  sorry

end PalindromicPrime
