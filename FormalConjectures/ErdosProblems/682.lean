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
# Erdős Problem 682

*Reference:* [erdosproblems.com/682](https://www.erdosproblems.com/682)

For almost all $n$, there exists an integer $m$ strictly between consecutive primes
$p_n$ and $p_{n+1}$ whose least prime factor is at least as large as the prime gap
$p_{n+1} - p_n$.

Erdős originally conjectured this for all sufficiently large $n$, but a conditional
counterexample via Dickson's conjecture shows this fails: if infinitely many pairs
$(2183 + 30030d, 2201 + 30030d)$ are both prime, they form consecutive primes with no
suitable $m$, since $30030 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ divides every
integer in the interval.

See also Erdős Problems 680 and 681. OEIS: [A386978](https://oeis.org/A386978).

[GaTa25] Gafni, A., Tao, T., _Rough numbers between consecutive primes_. arXiv:2508.06463
(2025).
-/

open Nat Classical Set

namespace Erdos682

/--
Erdős Problem 682: For almost all $n$, there exists an integer $m$ strictly
between consecutive primes $p_n$ and $p_{n+1}$ whose least prime factor is at
least as large as the prime gap $p_{n+1} - p_n$.

"Almost all" is formalized as: the exceptional set has natural density zero.

Proved by Gafni and Tao [GaTa25].
-/
@[category research solved, AMS 11]
theorem erdos_682 :
    {n : ℕ | ¬ ∃ m : ℕ, nth Nat.Prime n < m ∧ m < nth Nat.Prime (n + 1) ∧
      primeGap n ≤ minFac m}.HasDensity 0 := by
  sorry

end Erdos682
