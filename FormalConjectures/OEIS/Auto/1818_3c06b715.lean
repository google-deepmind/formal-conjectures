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

open Nat Finset Matrix

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 1 := by
  rfl

theorem a_two : a 2 = 9 := by
  rfl

theorem a_three : a 3 = 225 := by
  rfl

-- Define the characteristic function f(j, k) for the matrix entries.
-- Indices i and j here are the 1-based indices {1, ..., p-1}.
noncomputable def f_entry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    -- We perform arithmetic on integers before coercing to ensure subtraction is exact.
    let i_int : ℤ := i
    let j_int : ℤ := j
    -- i - j is guaranteed to be a unit in ZMod (p^2) because p is prime and 1 ≤ |i - j| ≤ p-2.
    let num : R := (i_int + j_int)
    let den : R := (i_int - j_int)
    num * den⁻¹

/--
Conjecture 2 from A001818: Let p be an odd prime. Then the permanent of the (p-1) X (p-1) matrix
[f(j,k)]_{j,k=1..p-1} is congruent to a((p-1)/2) = ((p-2)!!)^2 modulo p^2,
where f(j,k) is (j+k)/(j-k) if j is not equal to k, and f(j,k) = 1 otherwise.
-/
theorem oeis_1818_conjecture_2 {p : ℕ} (hp : p.Prime) (h_odd : p ≠ 2) :
  let N : ℕ := p - 1
  let R := ZMod (p ^ 2)
  let Idx := Fin N
  -- M is the (p-1) x (p-1) matrix.
  -- We map the Fin N indices (0 to N-1) to the 1-based indices (1 to N).
  let M : Matrix Idx Idx R := fun i j =>
    f_entry (i.val + 1) (j.val + 1)
  (M.permanent : R) = (a ((p - 1) / 2) : R) := by sorry
