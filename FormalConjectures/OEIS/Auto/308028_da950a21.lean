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
A308028: Number of ways to write $2n+1$ as $p + q + r$ with $2p + 4q + 6r$ a square, where $p,q,r$ are odd primes.
-/
def A308028 (n : ℕ) : ℕ :=
  let N := 2 * n + 1

  -- Summation over all possible natural numbers p and q up to N.
  (range (N + 1)).sum fun p =>
    (range (N + 1)).sum fun q =>
      -- Check if p + q leaves a positive remainder r.
      if p + q < N then
        let r := N - p - q
        let C := 2 * p + 4 * q + 6 * r

        -- Check all conditions: p, q, r are odd primes AND 2p+4q+6r is a square.
        if (p.Prime ∧ p ≠ 2) ∧
           (q.Prime ∧ q ≠ 2) ∧
           (r.Prime ∧ r ≠ 2) ∧
           (C.sqrt * C.sqrt = C)
        then 1 else 0
      else 0

theorem a_one : A308028 1 = 0 := by
  rfl

theorem a_two : A308028 2 = 0 := by
  rfl

theorem a_three : A308028 3 = 0 := by
  rfl

/--
The 2-4-6 Conjecture: a(n) > 0 for all n > 6. In other words, any odd integer greater than 14 can be written as the sum of three odd primes p,q,r for which 2*p + 4*q + 6*r is an integer square.
-/
theorem oeis_308028_conjecture_1 : ∀ (n : ℕ), 6 < n → 0 < A308028 n :=
by sorry
