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

/--
A214560: Number of 0's in binary expansion of $n^2$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 0 := by
  delta a
  norm_num [List.count]

theorem a_two : a 2 = 2 := by
  norm_num[a, not_iff]

theorem a_three : a 3 = 2 := by
  delta a
  push_cast+decide[↑(2).digits_def', (@2).digits_zero]


/-- Conjecture: for every x>=0 there is an i such that a(n)>x for n>i. -/
theorem oeis_214560_conjecture_1 : ∀ (x : ℕ), ∃ (i : ℕ), ∀ (n : ℕ), i < n → a n > x := by
  sorry
