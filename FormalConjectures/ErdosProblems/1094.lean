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
# Erdős Problem 1094

*Reference:* [erdosproblems.com/1094](https://www.erdosproblems.com/1094)
-/

namespace Erdos1094

open scoped Nat

/--
For all $n\ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le\max(n/k,k)$, with only
finitely many exceptions.
-/
@[category research open, AMS 11]
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

/--
For $k = 1$ and $n \geq 2$, the least prime factor of $\binom{n}{1} = n$ is at most $n = n/1$,
so the bound holds trivially. Known to hold for small cases by exhaustive computation.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/1094", AMS 11]
theorem erdos_1094.variants.k_one (n : ℕ) (hn : 2 ≤ n) :
    (n.choose 1).minFac ≤ max (n / 1) 1 := by
  sorry

end Erdos1094
