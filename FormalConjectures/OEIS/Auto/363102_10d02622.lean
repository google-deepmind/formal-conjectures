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
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$
-/
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

/--
A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  -- The subtraction n^2 - 2 is safe for n >= 3.
  num / Nat.gcd num denom_arg

/-- A363102 Conjecture 1: The sequence contains only 1's and primes. -/
theorem oeis_a363102_conjecture_1 :
  ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
  sorry
