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

import FormalConjecturesUtil

/-!
# Representations as $p + 2^x + 11 \cdot 2^y$ with $p \equiv 1 \pmod 6$

Number of ways to write the $n$-th positive odd integer in the form $p + 2^x + 11 \cdot 2^y$
with $p$ a prime congruent to $1 \bmod 6$ and $x, y$ positive integers.
$$a(n) = \left|\left\{(p, x, y) : p + 2^x + 11 \cdot 2^y = 2n - 1 \text{ with } p \text{ prime},
p \equiv 1 \pmod 6, x, y \in \mathbb{Z}^+\right\}\right|.$$

*References:*
- [A157237](https://oeis.org/A157237)
- Z.-W. Sun, "Mixed sums of primes and other terms", arXiv preprint
  [arXiv:0901.3075](https://arxiv.org/abs/0901.3075) [math.NT], 2009.-/

namespace OeisA157237

/-- Number of representations of $2n - 1$ as $p + 2^x + 11 \cdot 2^y$ with $p \equiv 1 \pmod 6$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N := 2 * n - 1
    ∑ x ∈ Finset.Icc 1 N,
    ∑ y ∈ Finset.Icc 1 N,
      if 2 ^ x + 11 * 2 ^ y < N ∧
         (N - (2 ^ x + 11 * 2 ^ y)).Prime ∧
         (N - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 16. -/
@[category test, AMS 11]
theorem a_16 : a 16 = 1 := by decide

/-- Value of the sequence `a` at 17. -/
@[category test, AMS 11]
theorem a_17 : a 17 = 1 := by decide

/-- Value of the sequence `a` at 18. -/
@[category test, AMS 11]
theorem a_18 : a 18 = 0 := by decide

/-- Value of the sequence `a` at 19. -/
@[category test, AMS 11]
theorem a_19 : a 19 = 2 := by decide

/--
On Feb. 24, 2009, Zhi-Wei Sun conjectured that $a(n) = 0$ if and only if $n < 16$ or
$n \in \{18, 21, 24, 51, 84, 1011, 59586\}$; in other words, except for
$35, 41, 47, 101, 167, 2021, 119171$, any odd integer greater than $30$ can be written as the
sum of a prime congruent to $1 \bmod 6$, a positive power of $2$ and eleven times a positive
power of $2$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586 := by
  sorry

end OeisA157237
