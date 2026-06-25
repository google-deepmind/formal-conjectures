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

*Reference:* [erdosproblems.com/493](https://www.erdosproblems.com/493)
-/

namespace Erdos493

/--
Is there some $k$ such that every sufficiently large integer $n$ can be written as
$\prod a_i - \sum a_i$ for integers $a_1, \ldots, a_k$ all at least $2$?

The answer is yes: already $k = 2$ suffices, since $n = (n + 2) \cdot 2 - ((n + 2) + 2)$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos493.lean"]
theorem erdos_493 :
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  sorry

end Erdos493
