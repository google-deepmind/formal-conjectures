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
A333095: the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{3n}$ evaluated at $x = 1$.
The sequence is defined by the sum of coefficients of the Taylor polynomial:
$$a(n) = \sum_{k = 0}^n \frac{3n}{3n+2k}\binom{3n+2k}{k} \quad \text{for } n \ge 1, \text{ and } a(0) = 1.$$
The result of the $\mathbb{Q}$ sum is known to be an integer, which justifies the floor/toNat conversion.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val
    ).floor).toNat


theorem a_zero : a 0 = 1 := by
  constructor

theorem a_one : a 1 = 4 := by
  simp_rw [a,]
  norm_num+decide only[ Finset.sum_range_succ, if_false, true,Nat.choose]

theorem a_two : a 2 = 34 := by
  delta a
  norm_num+decide only [ Finset.sum_range_succ,Nat.choose, if_false]

theorem a_three : a 3 = 337 := by
  delta a
  norm_num +decide only[Nat.choose, Finset.sum_range_succ, if_false]


/--
We conjecture that the sequence satisfies the stronger supercongruences
$a(n p^k) \equiv a(n p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333095_conjecture_0 (p n k : ℕ) :
  p.Prime → 5 ≤ p → 0 < n → 0 < k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry
