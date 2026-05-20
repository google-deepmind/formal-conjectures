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
A273917: Number of ordered ways to write $n$ as $w^2 + 3x^2 + y^4 + z^5$, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun w =>
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0

theorem a_one : a 1 = 1 := by
  decide

theorem a_two : a 2 = 2 := by
  decide

theorem a_three : a 3 = 1 := by
  decide

theorem a_four : a 4 = 2 := by
  decide

/--
Conjecture: a(n) > 0 for all n > 0.
This is part of a larger conjecture: "(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 3, 7, 11, 12, 15, 19, 24, 27, 31, 34, 35, 43, 46, 47, 56, 70, 71, 72, 87, 88, 115, 136, 137, 147, 167, 168, 178, 207, 235, 236, 267, 286, 297, 423, 537, 747, 762, 1017."
The claim A273917 Conjectures a(n) > 0 and (ii) verified up to 10^11 is also mentioned.
-/
theorem oeis_a273917_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  sorry
