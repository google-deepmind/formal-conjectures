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
# Erdős Problem 646

*Reference:* [erdosproblems.com/646](https://www.erdosproblems.com/646)

Let $p_1, \ldots, p_k$ be distinct primes. Are there infinitely many $n$ such that
$n!$ is divisible by an even power of each of the $p_i$?

The answer is yes, proved by Berend [Be97], who further proved that the
sequence of such $n$ has bounded gaps (where the bound depends on the initial
set of primes).

[Be97] Berend, D., *On the parity of exponents in the factorization of $n!$*. J. Number Theory **64** (1997), 13–19.
-/

namespace Erdos646

/--
Erdős Problem 646 (proved by Berend [Be97]):

For any finite set of primes, there are infinitely many $n$ such that
$n!$ is divisible by an even power of each prime in the set. Equivalently,
for each prime $p$ in the set, the $p$-adic valuation of $n!$ is even.
-/
@[category research solved, AMS 11]
theorem erdos_646 : answer(True) ↔
    ∀ (primes : Finset ℕ), (∀ p ∈ primes, Nat.Prime p) →
    Set.Infinite {n : ℕ | ∀ p ∈ primes, Even (padicValNat p n.factorial)} := by
  sorry

end Erdos646
