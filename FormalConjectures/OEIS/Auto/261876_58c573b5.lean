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

open Nat Finset BigOperators

/--
A261876: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2+7y^2+9z^2)yz$ a square, where $x,y,z,w$ are nonnegative integers with $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := IsSquare k

  -- Since $x^2 \le n$, a simple and safe iteration bound for all variables is $n+1$.
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if h_z : z > 0 then
      let k := x^2 + y^2 + z^2
      if h_le : k ≤ n then
        let r := n - k
        -- The existence of a natural number $w$ such that $w^2 = r$.
        if is_square r then
          let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
          -- The primary sequence condition: $(5x^2+7y^2+9z^2)yz$ must be a perfect square.
          if is_square condition_expr then 1 else 0
        else 0
      else 0
    else 0


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 3 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry

theorem a_four : a 4 = 1 := by
  sorry

/-- The set of base integers $m$ for which $a(n)=1$. -/
def special_m_set : Set ℕ :=
  {1, 7, 23, 647, 863}

/--
%C A261876 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m
(k = 0,1,2,... and m = 1, 7, 23, 647, 863).
-/
theorem oeis_261876_conjecture_0 (n : ℕ) :
  (n > 0 → a n > 0) ∧
  (a n = 1 ↔ ∃ k m : ℕ, special_m_set m ∧ n = 4^k * m) :=
by sorry
