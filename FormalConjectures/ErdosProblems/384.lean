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
# Erdős Problem 384

*Reference:* [erdosproblems.com/384](https://www.erdosproblems.com/384)

A conjecture of Erdős and Selfridge, proved by Ecklund [Ec69].

Ecklund made the stronger conjecture that whenever $n > k^2$ the binomial coefficient
$\binom{n}{k}$ is divisible by a prime $p < n/k$.

[Ec69] Ecklund, E. F., _On prime divisors of the binomial coefficient_ (1969).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos384

/--
Erdős Problem 384 [ErGr80, p.73]:

If $1 < k < n - 1$, then $\binom{n}{k}$ is divisible by some prime $p$ with
$2p < n$ (equivalently $p < n/2$), except when $(n, k) = (7, 3)$ or $(7, 4)$.
-/
@[category research solved, AMS 11]
theorem erdos_384 :
    ∀ n k : ℕ, 1 < k → k + 1 < n →
    ¬(n = 7 ∧ (k = 3 ∨ k = 4)) →
    ∃ p : ℕ, Nat.Prime p ∧ 2 * p < n ∧ p ∣ Nat.choose n k := by
  sorry

end Erdos384
