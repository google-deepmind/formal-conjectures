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

/-- `IsBuchi M` asserts that whenever `M` consecutive values `(x + n)² + a` (for
`n = 0, …, M - 1`) are all perfect squares, then `a` must be `0`. -/
def IsBuchi (M : ℕ) : Prop :=
  ∀ x a : ℤ, (∀ n ∈ Finset.range M, IsSquare ((x + (n : ℤ)) ^ 2 + a)) → a = 0

/--
**Büchi's problem**
There exists a positive integer $M$ such that, for all integers $x$ and $a$,
if $(x+n)^2 + a$ is a square for $M$ consecutive values of $n$, then $a = 0$.
-/
@[category research open, AMS 11]
theorem buchi_problem :
    answer(sorry) ↔ ∃ M : ℕ, 1 ≤ M ∧ IsBuchi M := by
  sorry


/--
**Büchi's problem (first open case, $M = 5$)**:
For all integers $x$ and $a$, if $(x+n)^2 + a$ is a perfect square for $n = 0, 1, 2, 3, 4$,
then $a = 0$.

Non-trivial sequences of length 3 and 4 are known to exist, so $M = 5$ is the first open case.
-/
@[category research open, AMS 11]
theorem buchi_problem_M5 :
    ∀ x a : ℤ,
      (∀ n ∈ Finset.range 5, IsSquare ((x + (n : ℤ)) ^ 2 + a)) →
      a = 0 := by
  sorry


end Buchi
