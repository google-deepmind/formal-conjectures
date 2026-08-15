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

/-- Computable check for $k = 4^a$ for some $a \ge 0$. -/
def is_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    -- k must be a power of 2 (k = 2^m) and its exponent m must be even.
    k = 2^m ∧ m % 2 = 0

/--
A337743: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 2y$ a power of four
(including $4^0 = 1$), where $x, y, z, w$ are nonnegative integers with $z \le w$.
-/
def A337743 (n : ℕ) : ℕ :=
  let max_x := sqrt n
  (range (max_x + 1)).sum fun x =>
    let n' := n - x^2
    let max_y := sqrt n'
    (range (max_y + 1)).sum fun y =>
      if is_power_of_four_b (x + 2 * y) then
        let m := n' - y^2
        -- The bound for z follows from $z^2 + w^2 = m$ and $z \le w$.
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          -- Check if $w^2 = w_{sq}$.
          if sqrt w_sq * sqrt w_sq = w_sq then
            1
          else
            0
      else
        0


theorem a_one : A337743 1 = 1 := by
  sorry

theorem a_two : A337743 2 = 1 := by
  sorry

theorem a_three : A337743 3 = 1 := by
  sorry

theorem a_four : A337743 4 = 1 := by
  sorry


/-- A337743 Conjecture 1: a(n) > 0 if n is neither of the form 4^k*(4*m+3) (k>=0, m>=0) nor of the form 2^(4*k+3)*101 (k>=0). In particular, a(n^2) > 0 and a(2*n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1 (n : ℕ) :
  ( (¬ ∃ (k m : ℕ), n = 4 ^ k * (4 * m + 3)) ∧
    (¬ ∃ (k : ℕ), n = 2 ^ (4 * k + 3) * 101) ) → A337743 n > 0 := by
  sorry

/-- In particular, a(n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1_squares (n : ℕ) (hn : n > 0) :
  A337743 (n ^ 2) > 0 := by
  sorry

/-- In particular, a(2*n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1_double_squares (n : ℕ) (hn : n > 0) :
  A337743 (2 * n ^ 2) > 0 := by
  sorry
