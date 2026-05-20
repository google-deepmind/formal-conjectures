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
A229969: Number of ways to write $n = x + y + z$ with $0 < x \le y \le z$ such that all the six
numbers $2x-1, 2y-1, 2z-1, 2xy-1, 2xz-1, 2yz-1$ are prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Icc 1 (n / 3)) fun x ↦
    Finset.sum (Icc x ((n - x) / 2)) fun y ↦
      let z := n - x - y

      if Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
         Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)
      then 1 else 0


theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 0 := by
  sorry

theorem a_four : a 4 = 0 := by
  sorry


/--
Conjecture: a(n) > 0 for all n > 5. Moreover, any integer n > 6 can be written
as x + y + z with x among 3, 4, 6, 10, 15 such that 2*y-1, 2*z-1, 2*x*y-1, 2*x*z-1, 2*y*z-1 are prime.
-/
theorem oeis_A229969_conjecture (n : ℕ) :
  (n > 5 → a n > 0) ∧
  (n > 6 → ∃ x y z : ℕ,
    x > 0 ∧ y > 0 ∧ z > 0 ∧      -- 0 < x, y, z
    x + y + z = n ∧
    x ≤ y ∧ y ≤ z ∧              -- x ≤ y ≤ z
    x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
    Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
    Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)) :=
by sorry
