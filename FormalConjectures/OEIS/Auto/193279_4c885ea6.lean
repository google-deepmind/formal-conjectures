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

open Finset Nat

/--
A193279: Number of distinct sums of distinct proper divisors of $n$.
The count excludes an empty subset of proper divisors that would give $0$ as a sum.
-/
def A193279 (n : ℕ) : ℕ :=
  let D := properDivisors n
  -- The set of all distinct sums of subsets of D, including the sum of the empty set (0).
  let S := D.powerset.image (fun s : Finset ℕ => s.sum id)
  -- The number of distinct sums, minus the single sum 0 from the empty set.
  S.card - 1


theorem a_one : A193279 1 = 0 := by
  rfl

theorem a_two : A193279 2 = 1 := by
  sorry

theorem a_three : A193279 3 = 1 := by
  sorry

theorem a_four : A193279 4 = 3 := by
  sorry

/--
%C A193279 a(n)=n if n is an even perfect number (is the converse true?)
-/
theorem oeis_193279_conjecture_0 (n : ℕ) :
  (Nat.Perfect n ∧ Even n) → A193279 n = n := by
  sorry
