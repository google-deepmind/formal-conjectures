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
import FormalConjecturesUtil

/-!
# Polynomial-time computability of comparisons of sums of square roots

This file formalizes the "Square-root sum problem"
which asks if one can decide in polynomial time on a Turing machine
whether the sum of the square roots of a list of naturals
is below a cutoff (or alternatively, below another such sum).

This problem is relevant to questions in computational geometry
(for example, in determining which of two polygonal paths in Euclidean space is longer).

*References:*
- [Wikipedia: List of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science)
- [Wikipedia: Square-root sum problem](https://en.wikipedia.org/wiki/Square-root_sum_problem)

-/

namespace PolyTime

open ComplexityTheory Real

/--
**The square-root sum problem (single sum version)**

A decision problem that asks, of a list of natural numbers and a threshold,
whether the sum of the square roots of the elements of the list is at most that threshold.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem) -/
noncomputable def squareRootSum (l : List ℕ) (t : ℕ) : Bool :=
  decide ((l.map fun n => √(n : ℝ)).sum ≤ t)

/--
**Is the square-root sum problem polynomial time (single sum version)?**

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem) -/
@[category research open, AMS 68]
theorem isPolyTime_squareRootSum :
    answer(sorry) ↔ IsPolyTime (fun (⟨l, t⟩ : List ℕ × ℕ) => squareRootSum l t) := by
  sorry

/--
**The square-root sum problem (two sum version)**

A decision problem that asks, of two lists of natural numbers,
whether the sum of the square roots of the elements of the first list
is at most the corresponding sum for the second list.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem) -/
noncomputable def squareRootSumTwoSided (l₁ l₂ : List ℕ) : Bool :=
  decide ((l₁.map fun n => √(n : ℝ)).sum ≤ (l₂.map fun n => √(n : ℝ)).sum)

/--
**Is the square-root sum problem polynomial time (two sum version)?**

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem) -/
@[category research open, AMS 68]
theorem isPolyTime_squareRootSumTwoSided :
    answer(sorry) ↔
      IsPolyTime (fun (⟨l₁, l₂⟩ : List ℕ × List ℕ) => squareRootSumTwoSided l₁ l₂) := by
  sorry

end PolyTime
