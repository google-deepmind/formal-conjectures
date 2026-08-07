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

open Nat BigOperators

/-- A number $k$ is a perfect square if $\lfloor \sqrt{k} \rfloor^2 = k$.
We define this as a Boolean-valued function to satisfy computability for use in summation. -/
def is_square_check (k : ℕ) : Bool := k.sqrt * k.sqrt = k

/--
A271644: Number of ordered ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ such that $w \cdot x + 2 \cdot x \cdot y + 2 \cdot y \cdot z$ is a square, where $w$ is a positive integer and $x, y, z$ are nonnegative integers.
-/
noncomputable def A271644 (n : ℕ) : ℕ :=
  -- All loop variables are bounded by $\lfloor\sqrt{n}\rfloor$, so we iterate through Nat.sqrt n + 1.
  let B := n.sqrt + 1

  -- w is a positive integer.
  Finset.sum
    ((Finset.range B).filter (fun w => w > 0))
    (fun w =>
      -- The bound for $x$ is $\sqrt{n - w^2}$.
      Finset.sum (Finset.range (Nat.sqrt (n - w^2) + 1)) fun x =>
          -- The bound for $y$ is $\sqrt{n - w^2 - x^2}$.
          Finset.sum (Finset.range (Nat.sqrt (n - (w^2 + x^2)) + 1)) fun y =>
              let quad_sum_sq := w^2 + x^2 + y^2
              -- Since the bounds make the subtraction valid in ℕ, z_sq represents $z^2$.
              let z_sq := n - quad_sum_sq

              if is_square_check z_sq then
                let z := z_sq.sqrt
                -- Check the auxiliary square condition: $w x + 2 x y + 2 y z$ must be a square.
                if is_square_check (w*x + 2*x*y + 2*y*z) then 1 else 0
              else 0
    )

-- The provided theorems are likely for testing, but I'll keep them as stubs.
theorem a_one : A271644 1 = 1 := by
  sorry

theorem a_two : A271644 2 = 3 := by
  sorry

theorem a_three : A271644 3 = 1 := by
  sorry

theorem a_four : A271644 4 = 1 := by
  sorry

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 3, 7, 15, 47, 71, 379, 4^k (k = 0,1,2,...).
-/
theorem oeis_A271644_conjecture_i :
  (∀ (n : ℕ), n > 0 → A271644 n > 0) ∧
  (∀ (n : ℕ), n > 0 →
    (A271644 n = 1 ↔
      n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 47 ∨ n = 71 ∨ n = 379 ∨ (∃ (k : ℕ), n = 4^k))) :=
by sorry
