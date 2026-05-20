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
A119563: Define $F(n) = 2^{2^n}+1 = n$-th Fermat number, $M(n) = 2^n-1$ = the $n$-th Mersenne number.
Then $a(n) = F(n)+M(n)-1 = 2^{2^n} + 2^n - 1$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1


-- These theorems were meant for illustration and cause issues with the compiler environment.
-- They are retained here without body for completeness or defined as `rfl`.
theorem a_zero : a 0 = 2 := rfl

theorem a_one : a 1 = 5 := rfl

theorem a_two : a 2 = 19 := rfl

theorem a_three : a 3 = 263 := rfl

/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?
-/
theorem oeis_a119563_conjecture : {n : ℕ | Nat.Prime (a n)}.Infinite := by sorry
