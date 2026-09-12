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
# Binary representation of primes that divide a number, in decimal

The value $a(n)$ is given by
$$ a(n) = \sum_{p \mid n, p \text{ prime}} 2^{\pi(p) - 1} $$
where $\pi(p) = \mathrm{primeCounting}(p)$ gives the 1-based index of the prime $p$.

*References:*
- [A087207](https://oeis.org/A087207)-/

namespace OeisA87207

/-- Binary representation of the prime factors of $n$, represented in decimal:
$a(n) = \sum_{p \in \mathrm{support}(\mathrm{factorization}(n))} 2^{\pi(p) - 1}$. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ (Nat.factorization n).support, 2 ^ (Nat.primeCounting p - 1)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide +native

/--
Starting at any $n$ and iterating the map $n \mapsto a(n)$, we will always reach $0$.
- _Antti Karttunen_, Jun 18,20 2017
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : ∃ k : ℕ, (a^[k]) n = 0 := by
  sorry

end OeisA87207
