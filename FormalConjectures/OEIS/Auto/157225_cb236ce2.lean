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
open scoped Nat.Prime

/--
A157225: Number of ways to write the $n$-th positive odd integer in the form $p+2^x+7 \cdot 2^y$
with $p$ a prime congruent to $5 \bmod 6$ and $x,y$ positive integers.
$$a(n) = \left|\left\{(p,x,y) : p+2^x+7 \cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 5 \bmod 6 \text{ and } x,y \in \mathbb{Z}_{>0}\right\}\right|$$
-/
noncomputable def A157225 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N : ℕ := 2 * n - 1
    -- Since $2^x$ and $7 \cdot 2^y$ must be less than $N$, $x$ and $y$ are effectively bounded by $\sim \log_2 N$.
    -- We use Nat.log 2 N + 1 as a safe upper bound for the range of exponents.
    let max_exp : ℕ := Nat.log 2 N + 1

    Finset.card $ (Finset.range max_exp).product (Finset.range max_exp) |>.filter (fun xy =>
      let x := xy.fst
      let y := xy.snd

      -- 1. $x, y$ are positive integers.
      1 ≤ x ∧ 1 ≤ y ∧

      let term_sum := 2 ^ x + 7 * 2 ^ y

      -- 2. $p = N - \text{term\_sum}$ must be a natural number, so term_sum < N.
      term_sum < N ∧

      let p := N - term_sum

      -- 3. $p$ must be a prime congruent to 5 mod 6.
      p.Prime ∧ p % 6 = 5
    )

/--
Zhi-Wei Sun conjectured that $a(n)=0$ if and only if $n < 11$ or $n \in \{13, 16, 992\}$;
in other words, except for $25, 31, 1983$, any odd integer greater than $20$ can be written as the sum
of a prime congruent to $5 \bmod 6$, a positive power of $2$ and seven times a positive power of $2$.
-/
theorem oeis_157225_conjecture_0 :
    ∀ (n : ℕ), A157225 n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992 := by
  sorry
