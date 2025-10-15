/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1065

*Reference:* [erdosproblems.com/1065](https://www.erdosproblems.com/1065)
-/

namespace Erdos1065

/--
Are there infinitely many primes $p$ such that $p$ = $2^k * q + 1$
for some prime $q$ and $k ≥ 0$?
 -/
@[category research open, AMS 11]
theorem erdos_1065a :
    Set.Infinite {p | ∃ (q : ℕ) (k : ℕ), p.Prime ∧ q.Prime ∧ p = 2^k * q + 1}
    ↔ answer(sorry) := by
  sorry

/--
Are there infinitely many primes $p$ such that $p$ = $2^k 3^l q + 1$
for some prime $q$ and $k ≥ 0$, $l >= 0$?
-/
@[category research open, AMS 11]
theorem erdos_1065b :
    Set.Infinite {p | ∃ (q : ℕ) (k : ℕ) (l : ℕ), p.Prime ∧ q.Prime ∧ p = 2^k * 3^l * q + 1}
    ↔ answer(sorry) := by
  sorry

end Erdos1065
