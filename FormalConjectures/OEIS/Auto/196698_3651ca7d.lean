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
A196698: Number of primes of the form $3^n \pm 3^k \pm 1$ with $0 \le k < n$.
-/
def A196698 (n : ℕ) : ℕ :=
  let p3n := 3 ^ n
  (Finset.range n).biUnion (fun k =>
    let p3k := 3 ^ k
    -- The four terms $3^n \pm 3^k \pm 1$:
    { p3n + p3k + 1,
      p3n + p3k - 1,
      p3n - p3k + 1,
      p3n - p3k - 1 }
  )
  |>.filter Nat.Prime
  |>.card


theorem a_one : A196698 1 = 2 := by
  -- The problem asks only for statement formalization, not proofs of examples.
  -- The provided definitions are already runnable examples.
  sorry

theorem a_two : A196698 2 = 4 := by
  sorry

theorem a_three : A196698 3 = 6 := by
  sorry

theorem a_four : A196698 4 = 8 := by
  sorry

/--
Conjecture: infinitely many elements of this sequence are equal to 0.
-/
theorem oeis_196698_conjecture_2 : ∀ M : ℕ, ∃ n : ℕ, n > M ∧ A196698 n = 0 := by
  sorry
