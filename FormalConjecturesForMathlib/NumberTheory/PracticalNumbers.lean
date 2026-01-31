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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases

/-!
# Practical numbers

A positive integer `n` is called a *practical number* if every positive integer `m ≤ n` can be
represented as a sum of distinct divisors of `n`.

*References*:
- [Wikipedia, Practical number](https://en.wikipedia.org/wiki/Practical_number)

## Main definitions

* `Nat.IsPractical`: A natural number `n` is practical if every positive integer `m ≤ n` can be
  expressed as a sum of distinct divisors of `n`.

## Examples

* 1 is practical (trivially, since its only divisor 1 sums to 1)
* 6 is practical: 1=1, 2=2, 3=3, 4=1+3, 5=2+3, 6=6
* 12 is practical

-/

namespace Nat

/-- The set of subset sums of divisors of `n`, i.e., all sums of distinct divisors of `n`. -/
def divisorSubsetSums (n : ℕ) : Set ℕ :=
  {m | ∃ B : Finset ℕ, B ⊆ n.divisors ∧ m = ∑ i ∈ B, i}

/-- A natural number `n` is *practical* if every positive integer `m ≤ n` can be represented
as a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  ∀ m, 0 < m → m ≤ n → m ∈ divisorSubsetSums n

/-! ### Examples -/

/-- 1 is a practical number. -/
example : IsPractical 1 := by
  intro m hm hle
  interval_cases m
  exact ⟨{1}, by decide, rfl⟩

/-- 6 is a practical number: 1=1, 2=2, 3=3, 4=1+3, 5=2+3, 6=6. -/
example : IsPractical 6 := by
  intro m hm hle
  interval_cases m
  · exact ⟨{1}, by decide, rfl⟩
  · exact ⟨{2}, by decide, rfl⟩
  · exact ⟨{3}, by decide, rfl⟩
  · exact ⟨{1, 3}, by decide, by decide⟩
  · exact ⟨{2, 3}, by decide, by decide⟩
  · exact ⟨{6}, by decide, rfl⟩

/-- 12 is a practical number. -/
example : IsPractical 12 := by
  intro m hm hle
  interval_cases m
  · exact ⟨{1}, by decide, rfl⟩
  · exact ⟨{2}, by decide, rfl⟩
  · exact ⟨{3}, by decide, rfl⟩
  · exact ⟨{4}, by decide, rfl⟩
  · exact ⟨{1, 4}, by decide, by decide⟩
  · exact ⟨{6}, by decide, rfl⟩
  · exact ⟨{1, 6}, by decide, by decide⟩
  · exact ⟨{2, 6}, by decide, by decide⟩
  · exact ⟨{3, 6}, by decide, by decide⟩
  · exact ⟨{4, 6}, by decide, by decide⟩
  · exact ⟨{1, 4, 6}, by decide, by decide⟩
  · exact ⟨{12}, by decide, rfl⟩

end Nat
