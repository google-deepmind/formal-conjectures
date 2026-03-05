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
# Erdős Problem 683

*Reference:* [erdosproblems.com/683](https://www.erdosproblems.com/683)

A problem of Erdős [Er76d][Er79d]. The Sylvester-Schur theorem states that
$P\left(\binom{n}{k}\right) > k$ if $k \leq n/2$. Erdős [Er55d] proved that there exists
some $c > 0$ such that $P\left(\binom{n}{k}\right) \gg k \log k$ whenever $k \leq n/2$.
-/

open Real

namespace Erdos683

/-- The largest prime factor of $n$, or $1$ if $n$ has no prime factors (convention). -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldl max 1

/--
Erdős Problem 683 [Er76d][Er79d]: Is it true that there exists a constant $c > 0$ such that
for every $1 \leq k \leq n$, the largest prime factor of $\binom{n}{k}$ satisfies
$$P\left(\binom{n}{k}\right) \geq \min(n - k + 1,\; k^{1+c})?$$
-/
@[category research open, AMS 11]
theorem erdos_683 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      (largestPrimeFactor (Nat.choose n k) : ℝ) ≥
        min (↑(n - k + 1)) ((k : ℝ) ^ (1 + c)) := by
  sorry

end Erdos683
