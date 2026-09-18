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

import FormalConjecturesUtil

/-!
# Ways to write $n$ as the sum of three elements of $\{\lfloor T(x)/3 \rfloor : x \ge 1\}$

The sequence $a(n)$ counts the number of ways to write $n$ as the sum of three unordered elements
of the set $\{\lfloor T(x)/3 \rfloor : x = 1, 2, 3, \dots\}$, where $T(x) = \frac{x(x+1)}{2}$ is
the $x$-th triangular number.

*References:*
- [A256544](https://oeis.org/A256544)
-/

namespace OeisA256544

open Nat Finset

/-- The $x$-th triangular number $T(x) = \frac{x(x+1)}{2}$. -/
def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

/-- The finite set of values $v \in \{\lfloor T(x)/3 \rfloor : x \ge 1\}$ with $v \le n$. -/
def aElements (n : ℕ) : Finset ℕ :=
  let maxRange : ℕ := 4 * n + 2
  ((range maxRange).image (fun x : ℕ => triangular x.succ / 3)).filter (fun v => v ≤ n)

/-- The primary sequence $a(n)$: number of ways to write $n$ as the sum of three unordered
elements of $\{\lfloor T(x)/3 \rfloor : x \ge 1\}$. -/
def a (n : ℕ) : ℕ :=
  let vs := aElements n
  ∑ a ∈ vs, ∑ b ∈ vs,
    (vs.filter (fun c => a ≤ b ∧ b ≤ c ∧ a + b + c = n)).card

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by native_decide

/-- Conjecture: For any positive integer $m$, every nonnegative integer $n$ can be written as
$\lfloor T(x)/m \rfloor + \lfloor T(y)/m \rfloor + \lfloor T(z)/m \rfloor$ with $x, y, z$
nonnegative integers. -/
@[category research open, AMS 11]
theorem conjecture (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  sorry

end OeisA256544
