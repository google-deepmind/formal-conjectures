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
# Büchi's problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/B%C3%BCchi%27s_problem)
-/

namespace Buchi

/--
**Büchi's problem**
There exists a positive integer M such that, for all integers x and a,
if $(x+n)^2 + a$ is a square for M consecutive values of n, then a = 0.
-/
@[category research open, AMS 11]
theorem buchi_problem :
    answer(sorry) ↔
      ∃ M : ℕ, 1 ≤ M ∧ ∀ x a : ℤ,
        (∀ n ∈ Finset.range M, IsSquare ((x + (n : ℤ)) * (x + (n : ℤ)) + a)) →
        a = 0 := by
  sorry

end Buchi
