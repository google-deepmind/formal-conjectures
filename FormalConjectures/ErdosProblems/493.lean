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

*References:*
- [erdosproblems.com/493](https://www.erdosproblems.com/493)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221-254.
-/

namespace Erdos493

/--
Does there exist a $k$ such that every sufficiently large integer can be written in the form
\[\prod_{i=1}^k a_i - \sum_{i=1}^k a_i\]
for some integers $a_i\geq 2$?

Erdős attributes this question to Schinzel. Eli Seamans has observed that the answer is yes (with $k=2$) for a very simple reason: $n = 2(n+2)-(2+(n+2))$. There may well have been some additional constraint in the problem as Schinzel posed it, but [Er61] does not record what this is.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos493.lean"]
theorem erdos_493 : answer(True) ↔
    ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      ∃ a : Fin k → ℤ,
        (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
        (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  sorry

end Erdos493
