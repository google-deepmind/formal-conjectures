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
A261307: $a(n+1) = \left|a(n) - \gcd(a(n), 7n+6)\right|$, $a(1) = 1$.
The function is 1-indexed conceptually, with $a(n)$ giving the $n$-th term. We define $a(0)$ as a dummy value.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Dummy value for a(0)
  | 1 => 1 -- Base case a(1)
  | n' + 2 => -- For n >= 2. Let $m = n'+2$ be the current index.
    -- The previous index is $j = n'+1 = m-1$.
    let j := n' + 1
    let a_j := a j
    -- The argument for gcd is $7j+6$.
    let k := 7 * j + 6
    let g := Nat.gcd a_j k
    -- Compute the absolute difference using integer casting and natAbs.
    Int.natAbs ((a_j : ℤ) - (g : ℤ))


theorem a_one : a 1 = 1 := by
  rfl

theorem a_two : a 2 = 0 := by
  -- a(2) = |a(1) - gcd(a(1), 7*1+6)| = |1 - gcd(1, 13)| = |1-1| = 0
  sorry

theorem a_three : a 3 = 20 := by
  -- a(3) = |a(2) - gcd(a(2), 7*2+6)| = |0 - gcd(0, 20)| = |0 - 20| = 20
  sorry

/--
It is conjectured that for all $n > 2$, $a(n) = 0$ implies that $7n+6 = a(n+1)$ is prime, cf. A186259.
-/
theorem oeis_261307_conjecture_0 : ∀ (n : ℕ), n > 2 → a n = 0 → Nat.Prime (7 * n + 6) := by
  sorry
