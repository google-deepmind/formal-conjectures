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
# Infinitude of Mersenne primes

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mersenne_prime)
-/

namespace MersennePrimes

/--
A Mersenne prime is a prime number of the form `2ᵖ-1`.
-/
def IsMersennePrime (p : ℕ) : Prop :=
  Nat.Prime (2^p - 1)

/--
Are there infinitely many Mersenne primes?
-/
@[category research open, AMS 11]
theorem infinitely_many_mersenne_primes :
  Set.Infinite { p : ℕ | IsMersennePrime p } ↔ answer(sorry) := by
    sorry

end MersennePrimes
