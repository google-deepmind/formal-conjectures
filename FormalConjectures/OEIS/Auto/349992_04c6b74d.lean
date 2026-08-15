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
A349992: Number of ways to write $n$ as $x^4 + y^2 + (z^2 + 2 \cdot 4^w)/3$, where $x, y, z$ are nonnegative integers, and $w$ is 0 or 1.
The definition counts the number of quadruples $(x, y, z, w)$ in the bounded non-negative integer domain that satisfy the constraints.
-/
def A349992 (n : ℕ) : ℕ :=
  -- Using tight, but correct upper bounds for iteration variables to keep the definition computationally reasonable.
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt n) + 1
  let bound_y : ℕ := Nat.sqrt n + 1
  let bound_z : ℕ := (3 * n).sqrt + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range bound_z).sum fun z =>
  (range 2).sum fun w =>
      let num_z_term : ℕ := z ^ 2 + 2 * (4 ^ w)

      -- Condition 1: The term $(z^2 + 2 \cdot 4^w)/3$ must be a natural number.
      if num_z_term % 3 = 0 then
        -- Condition 2: The sum must equal n.
        if n = x ^ 4 + y ^ 2 + num_z_term / 3 then
          1
        else
          0
      else
        0

@[simp] theorem a_one : A349992 1 = 1 := by sorry
@[simp] theorem a_two : A349992 2 = 3 := by sorry
@[simp] theorem a_three : A349992 3 = 4 := by sorry
@[simp] theorem a_four : A349992 4 = 4 := by sorry


/--
The generalized number of representations count $n$ as
$a \cdot x^4 + b \cdot y^2 + (z^2 + c \cdot 4^w)/m$,
where $x, y, z \in \mathbb{N}$ and $w \in \{0, 1\}$.
We only need this function to be $> 0$.
Since $a, b, m \ge 1$ for all relevant tuples, we use division `n/a`, `n/b`.
The bounds use `Nat.sqrt` which correctly computes the integer floor of the square root.
-/
def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Bound for x: x^4 <= n/a => x <= (n/a)^(1/4)
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt (n / a)) + 1
  -- Bound for y: y^2 <= n/b => y <= (n/b)^(1/2)
  let bound_y : ℕ := Nat.sqrt (n / b) + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range 2).sum fun w =>
    let full_sum : ℕ := a * x ^ 4 + b * y ^ 2
    let c_term : ℕ := c * 4 ^ w

    -- Check if the remaining part of n is positive
    if full_sum < n ∧ m > 0 then
      -- We are looking for z such that: m * (n - full_sum) = z^2 + c_term
      let target_z2 : ℕ := m * (n - full_sum) - c_term

      -- Check that z^2 is non-negative (i.e., c_term <= m * (n - full_sum))
      -- and that the resulting target is a perfect square.
      if c_term ≤ m * (n - full_sum) ∧ (Nat.sqrt target_z2) ^ 2 = target_z2 then
        1
      else
        0
    else
      0

/--
A349992 Conjecture 2: If $(a,b,c,m)$ is one of the ordered tuples (1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32), (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48), (4,1,23,48), then each $n = 1, 2, 3, \dots$ can be written as $a \cdot x^4 + b \cdot y^2 + (z^2 + c \cdot 4^w)/m$, where $x,y,z$ are nonnegative integers, and $w$ is 0 or 1.
We have verified Conjecture 2 for n up to 2*10^5.
-/
theorem oeis_349992_conjecture_2 :
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32),
     (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48),
     (4,1,23,48)]
  ∀ (t : ℕ × ℕ × ℕ × ℕ) (h_t : t ∈ tuples) (n : ℕ),
    n > 0 →
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    generalized_A349992 a b c m n > 0
  := by sorry
