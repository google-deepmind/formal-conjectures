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
A157237: Number of ways to write the $n$-th positive odd integer in the form
$p + 2^x + 11 \cdot 2^y$ with $p$ a prime congruent to $1 \pmod 6$ and $x, y$ positive integers.
$$a(n)=|\{(p,x,y): p+2^x+11\cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 1 \pmod 6 \text{ and } x,y \in \mathbb{Z}^+\}|$$
Note: The sequence is often indexed from $n=1$, so $n$ is a positive natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  -- Upper bound for exponents $x$ and $y$. Since $2^k \le 2n-1$, $k \le \log_2(2n-1)$.
  -- $N.log2$ is $\lfloor \log_2 N \rfloor$. We can use a conservative bound.
  let B : ℕ := N.log2 + 1

  -- Range for $x$ and $y$ from 1 to B. The Finset should only contain positive integers.
  -- Finset.Icc 1 B is a safe way to get $\{1, 2, \dots, B\}$.
  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B

  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd

    let sum_of_powers := 2 ^ x + 11 * 2 ^ y

    -- Check if $p$ is positive.
    if N > sum_of_powers then
      let p := N - sum_of_powers
      -- Prime condition: p must be prime AND p % 6 = 1.
      if Nat.Prime p ∧ p % 6 = 1 then 1 else 0
    else
      0

-- The provided initial theorems a_one, a_two, etc., are omitted here as they are proofs
-- of specific values, and the goal is to formalize the conjecture.

/--
Conjecture A157237 (Zhi-Wei Sun, 2009):
The number of ways to write the $n$-th positive odd integer in the form $p + 2^x + 11 \cdot 2^y$,
where $p$ is a prime $\equiv 1 \pmod 6$ and $x, y \ge 1$, is zero if and only if
$n \in \{1, 2, \dots, 15, 18, 21, 24, 51, 84, 1011, 59586\}$.
-/
theorem oeis_A157237_sun_conjecture : ∀ n : ℕ, n > 0 → (a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586) :=
by sorry
