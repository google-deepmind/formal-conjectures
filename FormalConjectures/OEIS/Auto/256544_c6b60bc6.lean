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

/-- The triangular number $T(x) = x(x+1)/2$. -/
def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

/--
The set of values $V = \{ \lfloor T(x)/3 \rfloor : x \ge 1 \}$ that are less than or equal to $n$.
We generate values for $x \ge 1$ using $x \mapsto x.succ$ over a range, and rely on the filter $v \le n$ to constrain the set.
-/
def A256544_elements (n : ℕ) : Finset ℕ :=
  -- A liberal safe bound for $x$: $4n+2$ is sufficient since $T(x)/3$ grows quadratically.
  let max_range : ℕ := 4 * n + 2
  -- Use x.succ to ensure $x \ge 1$ generators.
  (range max_range).image (fun x : ℕ => (triangular x.succ) / 3)
    |> Finset.filter (fun v => v ≤ n)

/--
A256544: Number of ways to write $n$ as the sum of three unordered elements of the set $\{ \lfloor T(x)/3 \rfloor : x = 1, 2, 3, \dots \}$, where $T(x)$ denotes the triangular number $x(x+1)/2$.
This is computed by counting the number of ordered triples $(a, b, c)$ from the set $V$ such that $a \le b \le c$ and $a + b + c = n$.
-/
def A256544 (n : ℕ) : ℕ :=
  let Vs := A256544_elements n

  -- Iterate over all $a, b, c \in Vs$ and count those that satisfy the ordered sum.
  Vs.sum fun a =>
    Vs.sum fun b =>
      -- The constraint a + b + c = n means we only need to check c.
      (Vs.filter fun c =>
        a ≤ b ∧ b ≤ c ∧ a + b + c = n
      ).card


theorem a_zero : A256544 0 = 1 := by
  sorry

theorem a_one : A256544 1 = 1 := by
  sorry

theorem a_two : A256544 2 = 2 := by
  sorry

theorem a_three : A256544 3 = 3 := by
  sorry

/--
Conjecture: For any positive integer m, every nonnegative integer n can be written as
floor(T(x)/m) + floor(T(y)/m) + floor(T(z)/m) with x,y,z nonnegative integers.
-/
theorem oeis_256544_conjecture_0 (m : ℕ) (hm : m > 0) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m :=
  by sorry
