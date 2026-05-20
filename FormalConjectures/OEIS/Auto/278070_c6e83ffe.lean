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
A278070: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)


theorem a_zero : A278070 0 = 1 := by
  rfl

theorem a_one : A278070 1 = 2 := by
  -- The sum is for k=0 and k=1.
  -- k=0: (1 choose 0) * ((1+0).pred choose 0) * 0! = 1 * (0 choose 0) * 1 = 1 * 1 * 1 = 1.
  -- k=1: (1 choose 1) * ((1+1).pred choose 1) * 1! = 1 * (1 choose 1) * 1 = 1 * 1 * 1 = 1.
  -- Sum = 1 + 1 = 2.
  rfl

theorem a_two : A278070 2 = 11 := by
  -- k=0: (2 choose 0) * (1 choose 0) * 0! = 1
  -- k=1: (2 choose 1) * (2 choose 1) * 1! = 2 * 2 * 1 = 4
  -- k=2: (2 choose 2) * (3 choose 2) * 2! = 1 * 3 * 2 = 6
  -- Sum = 1 + 4 + 6 = 11
  rfl

theorem a_three : A278070 3 = 106 := by
  sorry -- Skipping detailed proof, since the goal is formalization of the conjecture.

/--
We conjecture that a(n+k) == a(n) (mod k) for all n and k.
If true, then for each k, the sequence a(n) taken modulo k is a periodic sequence and the period divides k.
For example, modulo 7 the sequence becomes [1, 2, 4, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2, ...], apparently a periodic sequence of period 7.
-/
theorem oeis_278070_conjecture_0 : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  sorry
