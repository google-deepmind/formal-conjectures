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
# Singmaster's conjecture

Singmaster's conjecture says that for any integer $t>1$, the number of solutions to the equation:

`$\binom{n}{k} = t,\quad 1 \le k < n,$`

with $\binom{n}{k}$ being the numbers that appear in Pascal's triangle, is bounded by a global
constant $O(1)$.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Singmaster%27s_conjecture)
-/

namespace Singmaster

/--
The set of pairs (n, k) representing the solutions to the equation
`Nat.choose n k = t` for a given `t`, under the constraint `1 ≤ k < n`.
-/
def solutions (t : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ k < n ∧ Nat.choose n k = t}

@[category research open, AMS 11]
theorem singmaster: ∃ (C : ℕ), ∀ (t : ℕ), t > 1 →
    (Singmaster.solutions t).Finite ∧ (Singmaster.solutions t).ncard ≤ C := by
  sorry

end Singmaster
