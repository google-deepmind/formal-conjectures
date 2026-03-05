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

If $A \subseteq \{1, \ldots, n\}$ is such that $\operatorname{lcm}(a, b) > n$ for all distinct
$a, b \in A$, then $\sum_{a \in A} 1/a \leq 31/30$.

*Reference:* [erdosproblems.com/542](https://www.erdosproblems.com/542)
-/

open Finset BigOperators

namespace Erdos542

/--
Erdős Problem 542 (proved by Schinzel and Szekeres):
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
