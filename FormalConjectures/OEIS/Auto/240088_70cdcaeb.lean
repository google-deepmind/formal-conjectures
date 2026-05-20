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
The number of ways of writing $n$ as an ordered sum of a triangular number (A000217), a square (A000290) and a pentagonal number (A000326).
$$a(n) = \#\{(i, j, k) \in \mathbb{N}^3 \mid T_i + S_j + P_k = n\}$$
where $T_i = i(i+1)/2$, $S_j=j^2$, and $P_k=k(3k-1)/2$.
-/
def A240088 (n : ℕ) : ℕ :=
  let triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2
  let square_number (k : ℕ) : ℕ := k ^ 2
  let pentagonal_number (k : ℕ) : ℕ := k * (3 * k - 1) / 2

  -- A safe upper bound for all indices $i, j, k$.
  -- Since $T_i \le n \implies i^2 < 2n$, $\lfloor \sqrt{2n} \rfloor + 1$ is sufficient.
  let M : ℕ := Nat.sqrt (2 * n) + 1

  Finset.sum (Finset.range M) $ λ i =>
  Finset.sum (Finset.range M) $ λ j =>
  Finset.sum (Finset.range M) $ λ k =>
    if triangular_number i + square_number j + pentagonal_number k = n then 1 else 0


theorem a_zero : A240088 0 = 1 := by
  -- The actual proof for zero is:
  -- T_0 + S_0 + P_0 = 0 + 0 + 0 = 0. This is one way, and the only way.
  -- The definition of A240088 with bound M needs to be shown to yield 1.
  -- For n=0, M = Nat.sqrt(0) + 1 = 1. Finset.range 1 is {0}.
  -- The sum is for i=0, j=0, k=0: T_0 + S_0 + P_0 = 0. The if is 1. Sum is 1.
  -- The Finset.range M will be correct for this one.
  sorry

theorem a_one : A240088 1 = 3 := by
  sorry

theorem a_two : A240088 2 = 3 := by
  sorry

theorem a_three : A240088 3 = 2 := by
  sorry

/--
It is conjectured that a(n) is always positive.
This means that every natural number $n$ can be written as an ordered sum of a triangular number, a square, and a pentagonal number.
-/
theorem oeis_240088_conjecture : ∀ (n : ℕ), A240088 n > 0 := by
  sorry
