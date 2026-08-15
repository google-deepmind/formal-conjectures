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

/--
A007468: Sum of next $n$ primes.
The sequence is defined as the sum of the primes in the $n$-th row of the prime number triangle.
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} \operatorname{prime}_i$$
We use the Mathlib $k$-th prime function: $\operatorname{prime}(k) = \text{Nat.nth Nat.Prime } k$, indexed from 0.
The formula calculates the sum of $n$ primes starting at index $k_0 = n(n-1)/2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)


theorem a_one : a 1 = 2 := by
  sorry

theorem a_two : a 2 = 8 := by
  sorry

theorem a_three : a 3 = 31 := by
  sorry

theorem a_four : a 4 = 88 := by
  sorry

/-- Observation: a(38) is a perfect square. $a(38) = 207936 = 456^2$. -/
theorem a_38_is_square : IsSquare (a 38) := by
  sorry

/--
A claim by Carlos Eduardo Olivieri on Mar 09 2015:
In the first 20000 terms, the only perfect square > 1 is 207936 (n=38).
Is it the only one?

Conjecture: The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
-/
theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  sorry
