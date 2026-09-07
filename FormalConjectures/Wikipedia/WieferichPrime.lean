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
# Wieferich primes

A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$. The only known examples are
$1093$ and $3511$. It is conjectured that there are infinitely many Wieferich primes; a heuristic
argument suggests that the number of Wieferich primes up to $x$ grows like $\log \log x$.

*References:*
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* [OEIS A001220](https://oeis.org/A001220)
-/

namespace WieferichPrime

/-- There are infinitely many Wieferich primes. -/
@[category research open, AMS 11]
theorem infinite_isWieferichPrime : {p : ℕ | IsWieferichPrime p}.Infinite := by
  sorry

/-- The prime $1093$ is a Wieferich prime: $2^{1092} \equiv 1 \pmod{1093^2}$. -/
@[category test, AMS 11]
theorem isWieferichPrime_1093 : IsWieferichPrime 1093 := by
  decide +kernel

/-- The prime $11$ is not a Wieferich prime: $2^{10} \not\equiv 1 \pmod{11^2}$. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_11 : ¬ IsWieferichPrime 11 := by
  decide

/-- The prime $2$ is not a Wieferich prime, so no hypothesis excluding it is needed. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_two : ¬ IsWieferichPrime 2 := by
  decide

end WieferichPrime
