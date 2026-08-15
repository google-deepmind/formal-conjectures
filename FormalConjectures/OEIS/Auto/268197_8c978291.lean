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
A268197: Number of ordered ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ with $w \cdot (25w + 24x + 48y + 96z)$ a square, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def A268197 (n : ℕ) : ℕ :=
  -- Function to check if a natural number is a perfect square using the computable Nat.sqrt function.
  let is_square_check (m : ℕ) : Prop := (Nat.sqrt m) * (Nat.sqrt m) = m

  -- A safe upper bound for all variables is n. Finset.range (n+1) covers 0 to n.
  let B : ℕ := n + 1

  (Finset.range B).sum fun w =>
  (Finset.range B).sum fun x =>
  (Finset.range B).sum fun y =>
  (Finset.range B).sum fun z =>
    if w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ is_square_check (w * (25 * w + 24 * x + 48 * y + 96 * z)) then 1 else 0


theorem a_one : A268197 1 = 1 := by
  -- This is true by the definition and example a(1) = 1.
  sorry

theorem a_two : A268197 2 = 2 := by
  -- This is true by the definition and example a(2) = 2.
  sorry

theorem a_three : A268197 3 = 1 := by
  -- This is true by the definition and example a(3) = 1.
  sorry

theorem a_four : A268197 4 = 1 := by
  -- This is true by the sequence data and is $4^1 \cdot 1$.
  sorry

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 3, 7, 15, 23, 43, 55, 463, 4^k*m (k = 0,1,2,... and m = 1, 31, 34).
-/
theorem oeis_268197_conjecture_i :
  (∀ n : ℕ, n > 0 → A268197 n > 0) ∧
  (∀ n : ℕ, A268197 n = 1 ↔
    n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 23 ∨ n = 43 ∨ n = 55 ∨ n = 463 ∨
    (∃ k : ℕ, n = 4^k * 1 ∨ n = 4^k * 31 ∨ n = 4^k * 34)) :=
by sorry
