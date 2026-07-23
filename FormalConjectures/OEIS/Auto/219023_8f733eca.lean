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

open Nat Finset

/--
A219023: Number of primes $p<n$ such that $n^2-n+p$ and $n^2+n-p$ are both prime.
-/
def a (n : ℕ) : ℕ :=
  (Nat.primesBelow n).sum (fun p =>
    if (n ^ 2 - n + p).Prime ∧ (n ^ 2 + n - p).Prime then 1 else 0
  )

theorem a_one : a 1 = 0 := by
  simp [a, Nat.primesBelow]

theorem a_two : a 2 = 0 := by
  simp [a, Nat.primesBelow]

theorem a_three : a 3 = 0 := by
  simp [a, Nat.primesBelow]

theorem a_four : a 4 = 0 := by
  simp [a, Nat.primesBelow]

theorem oeis_219023_conjecture_1 (n : ℕ) (h : n > 2732) : a n > 0 := by
  sorry

/-- The conjecture is that a(n)>0 for all n>2732. -/
theorem oeis_219023_conjecture_stronger : ∀ n : ℕ, n > 2732 → a n > 0 := by
  sorry
