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
# Factorial primes

A factorial prime is a prime that is one more or one less than a factorial. It
is conjectured that there are infinitely many factorial primes.

*References:*
- [Wikipedia, Factorial prime](https://en.wikipedia.org/wiki/Factorial_prime)
- [OEIS A088054](https://oeis.org/A088054)
-/

namespace FactorialPrime

/-- A factorial prime is a prime one above or one below a factorial. -/
def IsFactorialPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ n : ℕ, p = n.factorial + 1 ∨ n.factorial = p + 1

@[category test, AMS 11]
theorem seven_isFactorialPrime : IsFactorialPrime 7 := by
  refine ⟨by norm_num, 3, Or.inl ?_⟩
  norm_num

@[category test, AMS 11]
theorem twentyThree_isFactorialPrime : IsFactorialPrime 23 := by
  refine ⟨by norm_num, 4, Or.inr ?_⟩
  norm_num

/-- There are infinitely many factorial primes. -/
@[category research open, AMS 11]
theorem infinitely_many_factorial_primes :
    Set.Infinite {p : ℕ | IsFactorialPrime p} := by
  sorry

end FactorialPrime
