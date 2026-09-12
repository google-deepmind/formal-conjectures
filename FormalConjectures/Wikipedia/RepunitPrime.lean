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
# Decimal Repunit Primes

A decimal repunit is a natural number whose decimal representation consists entirely of ones.
It is conjectured that infinitely many decimal repunits are prime.

*References:*
- [Wikipedia: Repunit](https://en.wikipedia.org/wiki/Repunit#Decimal_repunit_primes)
- [OEIS A002275](https://oeis.org/A002275)
- [OEIS A004022](https://oeis.org/A004022)
- [OEIS A004023](https://oeis.org/A004023)
-/

namespace RepunitPrime

/-- The decimal repunit of length $n$, defined as $1 + 10 + \cdots + 10^{n-1}$. -/
def repunit10 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 10 ^ i

@[category test, AMS 11]
theorem repunit10_one : repunit10 1 = 1 := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_two : repunit10 2 = 11 := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_three : repunit10 3 = 111 := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_four : repunit10 4 = 1111 := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_five : repunit10 5 = 11111 := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_two_prime : (repunit10 2).Prime := by
  norm_num [repunit10, Finset.sum_range_succ]

@[category test, AMS 11]
theorem repunit10_three_not_prime : ¬ (repunit10 3).Prime := by
  norm_num [repunit10, Finset.sum_range_succ, Nat.prime_def_lt]
  exact ⟨3, by norm_num, by norm_num, by norm_num⟩

/-- [Wikipedia's repunit article](https://en.wikipedia.org/wiki/Repunit#Decimal_repunit_primes)
states: "It has been conjectured that there are infinitely many repunit primes." -/
@[category research open, AMS 11]
theorem infinitely_many_repunit_primes :
    {n : ℕ | (repunit10 n).Prime}.Infinite := by
  sorry

end RepunitPrime
