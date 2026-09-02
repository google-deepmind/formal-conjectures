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
A020330: The sequence of bounds for prime counting, given by the formula
$A(n) = (2^{\lfloor \log_2 n \rfloor + 1} + 1) \cdot n$.
-/
noncomputable def a020330 (n : ℕ) : ℕ :=
  (2 ^ (log2 n + 1) + 1) * n

/--
A293833: Number of primes $p$ with $A020330(n) < p < A020330(n+1)$.
This count is given by $\pi(A_{020330}(n+1) - 1) - \pi(A_{020330}(n))$, where $\pi(x)$ is the prime-counting function $\mathtt{Nat.primeCounting}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let L := a020330 n
  let R := a020330 (n + 1)

  -- The prime counting function Nat.primeCounting gives the number of primes <= x.
  -- The number of primes $p$ s.t. $L < p < R$, is $\pi(R-1) - \pi(L)$.
  -- R - 1 is safe since R = a020330 (n+1) is large for n > 0.
  (R - 1).primeCounting - L.primeCounting


theorem a_one : a 1 = 2 := by sorry

theorem a_two : a 2 = 2 := by sorry

theorem a_three : a 3 = 5 := by sorry

theorem a_four : a 4 = 3 := by sorry

/--
Conjecture: $a(n) > 0$ for all $n > 0$, and $a(n) = 1$ only for $n = 12$.
This is an analog of Legendre's conjecture that for each $n = 1,2,3,...$ there is a prime between $n^2$ and $(n+1)^2$.
-/
theorem oeis_a293833_conjecture :
  ∀ n : ℕ, n > 0 → (a n > 0 ∧ (a n = 1 ↔ n = 12)) :=
by sorry
