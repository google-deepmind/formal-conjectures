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

open scoped BigOperators

/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

theorem a_one : a 1 = 1 := by
  simp_all[ a]

theorem a_two : a 2 = 2 := by
  norm_num[a]
  norm_num only[Nat.choose, Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton]

theorem a_three : a 3 = 6 := by
  norm_num[a ·]
  norm_num only[ Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton,Nat.choose]

theorem a_four : a 4 = 4 := by
  delta a
  norm_num only [ Finset.sum_Icc_succ_top,Nat.choose, Finset.Icc_self, Finset.sum_singleton]

/--
A175386 We conjecture that sum((1/i)*C(2n-i-1,i-1),i=1..n) is not an integer for $n>1$.
-/
theorem oeis_175386_conjecture_0 (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  sorry
