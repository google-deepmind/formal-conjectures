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
# Erdős Problem 453

*Reference:* [erdosproblems.com/453](https://www.erdosproblems.com/453)

Is it true that, for all sufficiently large $n$, there exists some $i < n$ such that
$p_n^2 < p_{n+i} \cdot p_{n-i}$, where $p_k$ is the $k$th prime?

Asked by Erdős and Straus. Selfridge conjectured the answer is no, contrary
to Erdős and Straus. The answer is no, as shown by Pomerance [Po79], who
proved there are infinitely many $n$ such that $p_n^2 > p_{n+i} \cdot p_{n-i}$
for all $0 < i < n$.

[Po79] Pomerance, C., _A note on the least prime in an arithmetic progression_.
-/

namespace Erdos453

/-- The $k$th prime (0-indexed): $p_0 = 2$, $p_1 = 3$, $p_2 = 5$, ... -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/--
Erdős Problem 453 (Disproved by Pomerance [Po79]):

Is it true that, for all sufficiently large $n$, there exists some $i < n$ such that
$p_n^2 < p_{n+i} \cdot p_{n-i}$? The answer is no.
-/
@[category research solved, AMS 11]
theorem erdos_453 : answer(False) ↔
    (∀ᶠ n in Filter.atTop, ∃ i : ℕ, 0 < i ∧ i < n ∧
      nthPrime n ^ 2 < nthPrime (n + i) * nthPrime (n - i)) := by
  sorry

/--
Pomerance [Po79] proved that there are infinitely many $n$ such that
$p_n^2 > p_{n+i} \cdot p_{n-i}$ for all $0 < i < n$.
-/
@[category research solved, AMS 11]
theorem erdos_453.variants.pomerance :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ i : ℕ, 0 < i → i < n →
        nthPrime (n + i) * nthPrime (n - i) <
          nthPrime n ^ 2 := by
  sorry

end Erdos453
