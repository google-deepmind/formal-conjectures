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

open Nat

/--
A341092: Rows of Pascal's triangle which contain a 3-term arithmetic progression of a certain form.
The $n$-th term (for $n \ge 1$) is defined by the piecewise formula:
$$a(2k-1)=(k+2)^2-2$$
$$a(2k)=(k+3)^2-4$$
where $k = \lceil n/2 \rceil = (n+1)/2$ using natural number division.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      -- n is odd, a(n) = (k+2)^2 - 2
      (k + 2) ^ 2 - 2
    else
      -- n is even, a(n) = (k+3)^2 - 4
      (k + 3) ^ 2 - 4

/--
A 4-term arithmetic progression in the $n$-th row of Pascal's triangle is a set of four distinct indices
$i < j < k < l \le n$ such that the binomial coefficients $\binom{n}{i}, \binom{n}{j}, \binom{n}{k}, \binom{n}{l}$ form an arithmetic progression.
This is equivalent to the conditions $2 \binom{n}{j} = \binom{n}{i} + \binom{n}{k}$ and $2 \binom{n}{k} = \binom{n}{j} + \binom{n}{l}$.
-/
def row_contains_ap_length_four (n : ℕ) : Prop :=
  ∃ i j k l : ℕ, -- Exist four indices i, j, k, l
    i < j ∧ j < k ∧ k < l ∧
    l ≤ n ∧ -- All indices must be within the bounds of the row n
    let a_coef := Nat.choose n i;
    let b_coef := Nat.choose n j;
    let c_coef := Nat.choose n k;
    let d_coef := Nat.choose n l;
    (2 * b_coef = a_coef + c_coef) ∧ (2 * c_coef = b_coef + d_coef)

/--
Conjecture 2 from OEIS A341092: No row contains an arithmetic progression of more than three coefficients.
This is formalized as the non-existence of a 4-term AP.
-/
theorem A341092_conjecture_2 : ∀ (n : ℕ), ¬row_contains_ap_length_four n :=
  by sorry
