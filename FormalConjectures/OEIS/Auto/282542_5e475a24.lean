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
A282542: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that $x + 3y + 5z$ is a square and (at least) one of $y,z,w$ are squares.
-/
def A282542 (n : ℕ) : ℕ :=
  (range (Nat.sqrt n + 1)).sum fun x =>
    (range (Nat.sqrt n + 1)).sum fun y =>
      (range (Nat.sqrt n + 1)).sum fun z =>
        (range (Nat.sqrt n + 1)).sum fun w =>
          if x^2 + y^2 + z^2 + w^2 = n ∧
             IsSquare (x + 3 * y + 5 * z) ∧
             (IsSquare y ∨ IsSquare z ∨ IsSquare w)
          then 1 else 0


theorem a_zero : A282542 0 = 1 := by
  sorry

theorem a_one : A282542 1 = 2 := by
  sorry

theorem a_two : A282542 2 = 2 := by
  sorry

theorem a_three : A282542 3 = 2 := by
  sorry

/--
Conjecture: a(n) > 0 for all n = 0,1,2,....
-/
theorem oeis_282542_conjecture_0 (n : ℕ) : A282542 n > 0 := by
  sorry
