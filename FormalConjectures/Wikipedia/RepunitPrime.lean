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
# Decimal Repunit Primes

A decimal repunit (`Nat.repunit 10 n`) is a natural number whose decimal representation consists
entirely of ones. It is conjectured that infinitely many decimal repunits are prime.

*References:*
- [Wikipedia: Repunit](https://en.wikipedia.org/wiki/Repunit#Decimal_repunit_primes)
- [OEIS A002275](https://oeis.org/A002275)
- [OEIS A004022](https://oeis.org/A004022)
- [OEIS A004023](https://oeis.org/A004023)
-/

@[expose] public section

namespace RepunitPrime

@[category test, AMS 11]
theorem repunit10_one : Nat.repunit 10 1 = 1 := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_two : Nat.repunit 10 2 = 11 := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_three : Nat.repunit 10 3 = 111 := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_four : Nat.repunit 10 4 = 1111 := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_five : Nat.repunit 10 5 = 11111 := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_two_prime : (Nat.repunit 10 2).Prime := by
  norm_num [Nat.repunit]

@[category test, AMS 11]
theorem repunit10_three_not_prime : ¬ (Nat.repunit 10 3).Prime := by
  norm_num [Nat.repunit, Nat.prime_def_lt]
  exact ⟨3, by norm_num, by norm_num, by norm_num⟩

/-- [Wikipedia's repunit article](https://en.wikipedia.org/wiki/Repunit#Decimal_repunit_primes)
conjectures that infinitely many base-$10$ repunits are prime. -/
@[category research open, AMS 11]
theorem infinitely_many_repunit_primes :
    {n : ℕ | (Nat.repunit 10 n).Prime}.Infinite := by
  sorry

end RepunitPrime
