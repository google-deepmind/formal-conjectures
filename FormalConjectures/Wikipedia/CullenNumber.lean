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
# Cullen primes

A *Cullen number* is a number of the form $C_n = n \cdot 2^n + 1$, where $n$ is a natural number,
and a *Cullen prime* is a Cullen number that is prime. The only known Cullen primes are those for
$n = 1, 141, 4713, 5795, 6611, 18496, \ldots$ ([OEIS A005849](https://oeis.org/A005849)). Hooley
showed that almost all Cullen numbers are composite, but it is conjectured that there are
infinitely many Cullen primes.

*References:*
- [Wikipedia: Cullen number](https://en.wikipedia.org/wiki/Cullen_number)
- [OEIS A005849](https://oeis.org/A005849)
- [EPSW03] Everest, G., van der Poorten, A., Shparlinski, I., and Ward, T., *Recurrence
  sequences*. Mathematical Surveys and Monographs 104, American Mathematical Society (2003), p. 94.
-/

@[expose] public section

namespace CullenNumber

/-- The `n`-th Cullen number $C_n = n \cdot 2^n + 1$. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- $C_1 = 3$ is a Cullen prime. -/
@[category test, AMS 11]
theorem cullen_one_prime : (cullen 1).Prime := by norm_num [cullen]

/-- $C_2 = 9$ is not prime. -/
@[category test, AMS 11]
theorem cullen_two_not_prime : ¬ (cullen 2).Prime := by norm_num [cullen]

/-- It is conjectured that there are infinitely many Cullen primes. -/
@[category research open, AMS 11]
theorem infinite_cullen_primes : {n : ℕ | (cullen n).Prime}.Infinite := by
  sorry

/-- Hooley showed that the set of $n$ for which $C_n$ is prime has natural density $0$
(see [EPSW03]). -/
@[category research solved, AMS 11]
theorem cullen_primes_hasDensity_zero : {n : ℕ | (cullen n).Prime}.HasDensity 0 := by
  sorry

/-- It is unknown whether there is a prime $p$ such that $C_p$ is also prime. -/
@[category research open, question, AMS 11]
theorem exists_prime_cullen_prime : ∃ p : ℕ, p.Prime ∧ (cullen p).Prime := by
  sorry

end CullenNumber
