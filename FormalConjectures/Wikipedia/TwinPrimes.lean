/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Twin prime conjecture

*References:*
- [Landau Problems Wikipedia Page](https://en.wikipedia.org/wiki/Landau%27s_problems#Twin_prime_conjecture)
- [Twin Primes Conjecture Wikipedia Page](https://en.wikipedia.org/wiki/Twin_prime#Twin_prime_conjecture)
- [OEIS A081947](https://oeis.org/A081947)
- [Prime Puzzles: Conjecture 32](https://www.primepuzzles.net/conjectures/conj_032.htm)
-/


namespace TwinPrimes

/-- A twin prime is a prime number with another prime at distance `2`. -/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p + 2).Prime ∨ (p - 2).Prime)

/--
Are there infinitely many primes p such that p + 2 is prime?
-/
@[category research open, AMS 11]
theorem twin_primes :
    answer(sorry) ↔ {p : ℕ | Prime p ∧ Prime (p + 2)}.Infinite := by
  sorry

/--
Dubner's conjecture: every even integer greater than `4208` is the sum of two twin primes.
-/
@[category research open, AMS 11]
theorem twin_primes.variants.dubner_conjecture (n : ℕ) (hn : 4208 < n) (hn_even : Even n) :
    ∃ p q, IsTwinPrime p ∧ IsTwinPrime q ∧ n = p + q := by
  sorry

end TwinPrimes
