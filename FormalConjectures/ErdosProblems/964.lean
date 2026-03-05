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
# Erdős Problem 964

*Reference:* [erdosproblems.com/964](https://www.erdosproblems.com/964)

Let $\tau(n)$ count the number of divisors of $n$. Is the sequence
$\tau(n+1)/\tau(n)$ everywhere dense in $(0,\infty)$?

This has been proved unconditionally by Eberhard [Eb25], who in fact showed
that every positive rational can be written as such a ratio.

[Er86b] Erdős, P., original problem statement.

[Eb25] Eberhard, S., proof that the sequence is dense.
-/

namespace Erdos964

/--
Erdős Problem 964 [Er86b]:

The set $\{\tau(n+1)/\tau(n) : n \geq 1\}$ is dense in $(0, \infty)$.

For every positive real $r$ and every $\varepsilon > 0$, there exists a natural number $n \geq 1$
such that $|\tau(n+1)/\tau(n) - r| < \varepsilon$.

Proved by Eberhard [Eb25].
-/
@[category research solved, AMS 11]
theorem erdos_964 : answer(True) ↔
    ∀ r : ℝ, r > 0 → ∀ ε : ℝ, ε > 0 →
    ∃ n : ℕ, n ≥ 1 ∧
      |((Nat.divisors (n + 1)).card : ℝ) / ((Nat.divisors n).card : ℝ) - r| < ε := by
  sorry

end Erdos964
