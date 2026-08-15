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

open Nat Set

/--
A354747: Start with $2n-1$; repeatedly triple and add 2 until reaching a prime.
$a(n)$ = number of steps until reaching a prime $> 2n-1$, or 0 if no prime is ever reached.
Equivalently, $a(n)$ is the smallest $m \ge 1$ such that $2 \cdot n \cdot 3^m - 1$ is prime.
-/
noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps


theorem a_one : a354747 1 = 1 := by
  push_cast[a354747]
  use IsLeast.csInf_eq ⟨ (by decide), ↑ fun and => And.left⟩

theorem a_two : a354747 2 = 1 := by
  push_cast[a354747]
  exact IsLeast.csInf_eq ⟨ (by decide), ↑ fun and=> And.left⟩

theorem a_three : a354747 3 = 1 := by
  push_cast[a354747]
  refine IsLeast.csInf_eq ⟨.symm (by·norm_num), ↑ fun and => And.left⟩

theorem a_four : a354747 4 = 1 := by
  norm_num[a354747]
  refine IsLeast.csInf_eq ⟨ (by decide), ↑ fun and =>And.left⟩


/-- The smallest unknown case is n = 100943. Is a(100943) = 0? -/
theorem oeis_a354747_conjecture_0 : a354747 100943 = 0 := by
  sorry
