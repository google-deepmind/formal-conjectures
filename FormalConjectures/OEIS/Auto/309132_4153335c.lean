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

open Rat Nat

/--
A309132: $a(n)$ is the denominator of $F(n) = A027641(n-1)/n + A027642(n-1)/n^2$,
where $A027641(k)$ and $A027642(k)$ are the numerator and denominator of the $k$-th standard Bernoulli number $B_k$ ($B_1 = -1/2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    have B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den

    -- F(n) = N / n + D / n^2, where division is rational division
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2

    F_n.den

theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 1 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

theorem a_four : a 4 = 16 := by
  sorry

/--
Conjecture: for $n > 1$, $a(n) = 1$ if and only if $n$ is prime.
This is the main conjecture related to A309132.
-/
theorem oeis_309132_conjecture_key (n : ℕ) (hn : n > 1) : a n = 1 ↔ Nat.Prime n := by
  sorry
