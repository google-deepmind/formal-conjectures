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

open Nat

/--
A038107: Number of primes $< n^2$.
This is the cardinality of the set of primes strictly less than $n^2$.
-/
def A038107 (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card


theorem a_zero : A038107 0 = 0 := by
  simp [A038107]

theorem a_one : A038107 1 = 0 := by
  simp only [A038107, one_pow]
  decide

theorem a_two : A038107 2 = 2 := by
  simp only [A038107, Nat.primesBelow, pow_two]
  decide

theorem a_three : A038107 3 = 4 := by
  simp only [A038107, pow_two]
  decide

/--
Conjecture: All the numbers Sum_{i=j,...,k} 1/a(i) with 1 < j <= k have pairwise distinct fractional parts.
-/
theorem oeis_38107_conjecture_2 :
  -- Define the reciprocal function, coercing A038107 i to a real number.
  let a_inv (i : ℕ) : ℝ := 1 / (A038107 i : ℝ)
  -- Iterate over two pairs of indices (j, k) and (j', k')
  ∀ j k j' k' : ℕ,
    -- Constraints 1 < j <= k
    1 < j → j ≤ k →
    -- Constraints 1 < j' <= k'
    1 < j' → j' ≤ k' →
    -- If their fractional parts are equal...
    Int.fract (Finset.sum (Finset.Icc j k) a_inv) = Int.fract (Finset.sum (Finset.Icc j' k') a_inv) →
    -- ...then the index pairs must be identical.
    (j, k) = (j', k') := by sorry
