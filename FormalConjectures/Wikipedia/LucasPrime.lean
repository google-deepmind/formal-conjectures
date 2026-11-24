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
# Infinitude of Lucas primes

The Lucas numbers $(L_n)_{n \ge 0}$ satisfy $L_0 = 2$, $L_1 = 1$, and $L_{n+2} = L_{n+1} + L_n$.
Prime terms $L_n$ (*Lucas primes*, OEIS A005479) occur at indices $n = 0, 2, 4, 5, 7, 8, \dots$
(OEIS A001606). Every positive index $n$ with $L_n$ prime is either prime itself or of the form
$2^k$. Whether infinitely many terms $L_n$ are prime remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- [Wikipedia: Lucas number](https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes)
- [OEIS A005479](https://oeis.org/A005479)
- [OEIS A001606](https://oeis.org/A001606)
-/

@[expose] public section

namespace LucasPrime

/-- Predicate asserting that the $n$-th Lucas number $L_n$ (`lucasNumber n`) is prime. -/
def IsLucasPrimeIndex (n : ℕ) : Prop :=
  (lucasNumber n).toNat.Prime

/-- Verifies that $L_0 = 2$ is a Lucas prime. -/
@[category test, AMS 11]
theorem isLucasPrimeIndex_zero : IsLucasPrimeIndex 0 := by
  unfold IsLucasPrimeIndex
  decide

/-- Verifies that $L_4 = 7$ is a Lucas prime. -/
@[category test, AMS 11]
theorem isLucasPrimeIndex_four : IsLucasPrimeIndex 4 := by
  unfold IsLucasPrimeIndex
  decide

/-- Verifies that $L_7 = 29$ is a Lucas prime. -/
@[category test, AMS 11]
theorem isLucasPrimeIndex_seven : IsLucasPrimeIndex 7 := by
  unfold IsLucasPrimeIndex
  decide

/-- Verifies that $L_1 = 1$ is not a Lucas prime. -/
@[category test, AMS 11]
theorem not_isLucasPrimeIndex_one : ¬ IsLucasPrimeIndex 1 := by
  unfold IsLucasPrimeIndex
  decide

/-- Verifies that $L_3 = 4$ is not a Lucas prime. -/
@[category test, AMS 11]
theorem not_isLucasPrimeIndex_three : ¬ IsLucasPrimeIndex 3 := by
  unfold IsLucasPrimeIndex
  decide

/--
Are infinitely many Lucas numbers $L_n$ prime?
-/
@[category research open, question, AMS 11]
theorem lucas_primes_infinitude :
    {n : ℕ | IsLucasPrimeIndex n}.Infinite := by
  sorry

/--
Every positive index $n$ with $L_n$ prime is either a prime number or of the form $2^k$.
-/
@[category textbook, AMS 11]
theorem lucas_prime_index_prime_or_two_pow {n : ℕ} (hn : 0 < n) (hp : IsLucasPrimeIndex n) :
    n.Prime ∨ ∃ k : ℕ, n = 2 ^ k := by
  sorry

end LucasPrime
