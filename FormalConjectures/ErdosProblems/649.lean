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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 649

*Reference:* [erdosproblems.com/649](https://www.erdosproblems.com/649)

Is it true that for any two primes $p, q$ there exists an integer $n$ such that
$P(n) = p$ and $P(n+1) = q$, where $P(m)$ denotes the greatest prime factor of $m$?

[Er95c] Erdős, P., *Some of my favourite problems which recently have been solved*.
-/

namespace Erdos649

/-- The greatest prime factor of $n$, or $0$ if $n \le 1$. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/--
Erdős Problem 649 (disproved):

Is it true that for any two primes $p, q$ there exists an integer $n$ such that
$P(n) = p$ and $P(n+1) = q$, where $P(m)$ denotes the greatest prime factor of $m$?

The answer is **no**. There are no solutions to $2^k \equiv -1 \pmod{7}$,
so this fails with $p = 2$ and $q = 7$. [Er95c]
-/
@[category research solved, AMS 11]
theorem erdos_649 : answer(False) ↔ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q →
    ∃ n : ℕ, 0 < n ∧ greatestPrimeFactor n = p ∧ greatestPrimeFactor (n + 1) = q := by
  sorry

end Erdos649
