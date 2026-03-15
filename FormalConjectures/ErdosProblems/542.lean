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
# Erdős Problem 542

Let $A \subseteq \{1, \ldots, n\}$ be such that $\operatorname{lcm}(a, b) > n$ for all distinct
$a, b \in A$.

1. Is it true that $\sum_{a \in A} 1/a \leq 31/30$?
2. Must there be $\gg n$ many integers $m \leq n$ that do not divide any element of $A$?

Schinzel and Szekeres answered (1) affirmatively and (2) negatively.
Chen later proved that for $n > 172509$, the sum is less than
$1/3 + 1/4 + 1/5 + 1/7 + 1/11$.

See also [Problem 784](https://www.erdosproblems.com/784).

## References

* [ScSz59] Schinzel, A., Szekeres, G., _Sur un problème de M. Paul Erdős_.
  Acta Sci. Math. (Szeged) (1959), 221–229.
* [Ch96] Chen, Y.-G., _On a problem of P. Erdős_.
  Acta Sci. Math. (Szeged) (1996), 101–114.
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_.
  A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ.,
  Fort Collins, Colo., 1971) (1973), 117–138.
* [Er98] Erdős, P., _Some of my new and almost new problems and results in
  combinatorial number theory_. Number theory (Eger, 1996) (1998), 169–180.

*Reference:* [erdosproblems.com/542](https://www.erdosproblems.com/542)
-/

open Finset BigOperators

namespace Erdos542

/--
Erdős Problem 542 (proved by Schinzel and Szekeres (1959) [ScSz59]):
If $A \subseteq \{1, \ldots, n\}$ is such that $\operatorname{lcm}(a, b) > n$ for all distinct
$a, b \in A$, then $\sum_{a \in A} 1/a \leq 31/30$.

The bound $31/30 = 1/2 + 1/3 + 1/5$ is best possible, as $A = \{2, 3, 5\}$ demonstrates.
-/
@[category research solved, AMS 5 11]
theorem erdos_542 :
    ∀ (n : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.lcm a b > n) →
      (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ≤ 31 / 30 := by
  sorry

end Erdos542
