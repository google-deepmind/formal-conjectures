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
# Erdős Problem 493

Does there exist a $k$ such that every sufficiently large integer can be written
in the form $\prod_i a_i - \sum_i a_i$ for some integers $a_i \geq 2$?

*Reference:* [erdosproblems.com/493](https://www.erdosproblems.com/493)

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
p. 238.
-/

open Finset BigOperators

namespace Erdos493

/--
Erdős Problem 493 (attributed to Schinzel):
Does there exist a $k$ such that every sufficiently large integer can be written
in the form $\prod_i a_i - \sum_i a_i$ for some integers $a_i \geq 2$?

The answer is yes with $k = 2$: for any integer $n$ we have
$n = 2 \cdot (n+2) - (2 + (n+2))$ (observed by Eli Seamans).
-/
@[category research solved, AMS 11]
theorem erdos_493 : answer(True) ↔
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, n ≥ N →
      ∃ a : Fin k → ℤ, (∀ i, a i ≥ 2) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  sorry

end Erdos493
