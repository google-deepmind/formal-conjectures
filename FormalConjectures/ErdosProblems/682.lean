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

[GaTa25] Gafni, A. and Tao, T., who showed the number of exceptional
$n \in [1, X]$ is $\ll X / (\log X)^2$.
-/

open Nat Classical

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
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.range N).filter (fun n =>
        ¬ ∃ m : ℕ, nth Nat.Prime n < m ∧ m < nth Nat.Prime (n + 1) ∧
          nth Nat.Prime (n + 1) - nth Nat.Prime n ≤ minFac m)).card : ℝ)
      ≤ ε * (N : ℝ) := by
  sorry

end Erdos682
