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
A281009: Number of odd divisors of $n$ minus the number of middle divisors of $n$.
A divisor $d$ of $n$ is a "middle divisor" if $\sqrt{n/2} \le d < \sqrt{2n}$,
which is equivalent to $n \le 2d^2$ and $d^2 < 2n$ for $d \in \mathbb{N}$.
-/
def A281009 (n : ℕ) : ℤ :=
  if h : n = 0 then
    0
  else
    let odd_div_count : ℕ := (divisors n).filter (fun d => d % 2 = 1) |>.card
    let middle_div_condition (d : ℕ) : Prop := n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n
    let middle_div_count : ℕ := (divisors n).filter middle_div_condition |>.card
    (odd_div_count : ℤ) - (middle_div_count : ℤ)

-- Placeholder theorems for example verification
theorem a_one : A281009 1 = 0 := by sorry
theorem a_two : A281009 2 = 0 := by sorry
theorem a_three : A281009 3 = 2 := by sorry
theorem a_four : A281009 4 = 0 := by sorry


/--
Conjecture 1: a(n) is also twice the number of odd divisors of n greater than sqrt(2*n).
-/
theorem oeis_281009_conjecture_0 (n : ℕ) (hn : n ≠ 0) :
    (A281009 n : ℤ) = 2 * (↑(((divisors n).filter (fun d => d % 2 = 1 ∧ 2 * n < d ^ 2)).card) : ℤ) :=
by sorry
