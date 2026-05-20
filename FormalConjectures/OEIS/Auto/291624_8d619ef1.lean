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
A291624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that $p = x + 2y + 5z$, $p - 2$ and $p + 4$ are all prime.
-/
def A291624 (n : ℕ) : ℕ :=
  let B : ℕ := sqrt n
  Finset.sum (Finset.range (B + 1)) fun x =>
  Finset.sum (Finset.range (B + 1)) fun y =>
  Finset.sum (Finset.range (B + 1)) fun z =>
    let sq_sum_xyz := x^2 + y^2 + z^2
    if sq_sum_xyz ≤ n then
      let r := n - sq_sum_xyz
      let w := sqrt r
      if w^2 = r then
        -- We have found a valid quadruple (x, y, z, w) such that x^2 + y^2 + z^2 + w^2 = n
        let p := x + 2 * y + 5 * z
        -- Check the prime triple condition. Note: p-2 is Nat.sub
        if Nat.Prime p ∧ Nat.Prime (p - 2) ∧ Nat.Prime (p + 4)
        then 1
        else 0
      else 0
    else 0


theorem a_one : A291624 1 = 0 := by
  sorry

theorem a_two : A291624 2 = 1 := by
  sorry

theorem a_three : A291624 3 = 1 := by
  sorry

theorem a_four : A291624 4 = 0 := by
  sorry


/-- Conjecture: a(n) > 0 for all n > 1 not divisible by 4. -/
theorem oeis_291624_conjecture_1 (n : ℕ) : n > 1 ∧ ¬ (4 ∣ n) → A291624 n > 0 := by
  sorry
