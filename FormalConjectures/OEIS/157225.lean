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
# Representations as $p + 2^x + 7 \cdot 2^y$ with $p \equiv 5 \pmod 6$

Number of ways to write the $n$-th positive odd integer in the form $p + 2^x + 7 \cdot 2^y$
with $p$ a prime congruent to $5 \bmod 6$ and $x, y$ positive integers.
$$a(n) = \left|\left\{(p, x, y) : p + 2^x + 7 \cdot 2^y = 2n - 1 \text{ with } p \text{ prime},
p \equiv 5 \pmod 6, x, y \in \mathbb{Z}^+\right\}\right|.$$

*References:*
- [A157225](https://oeis.org/A157225)
- Z.-W. Sun, "Mixed sums of primes and other terms", arXiv preprint
  [arXiv:0901.3075](https://arxiv.org/abs/0901.3075) [math.NT], 2009.-/

namespace OeisA157225

/-- Number of representations of $2n - 1$ as $p + 2^x + 7 \cdot 2^y$ with $p \equiv 5 \pmod 6$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N := 2 * n - 1
    ∑ x ∈ Finset.Icc 1 N,
    ∑ y ∈ Finset.Icc 1 N,
      if 2 ^ x + 7 * 2 ^ y < N ∧
         (N - (2 ^ x + 7 * 2 ^ y)).Prime ∧
         (N - (2 ^ x + 7 * 2 ^ y)) % 6 = 5 then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 11. -/
@[category test, AMS 11]
theorem a_11 : a 11 = 1 := by decide

/-- Value of the sequence `a` at 12. -/
@[category test, AMS 11]
theorem a_12 : a 12 = 1 := by decide

/-- Value of the sequence `a` at 13. -/
@[category test, AMS 11]
theorem a_13 : a 13 = 0 := by decide

/-- Value of the sequence `a` at 14. -/
@[category test, AMS 11]
theorem a_14 : a 14 = 2 := by decide

/--
On Feb. 24, 2009, Zhi-Wei Sun conjectured that $a(n) = 0$ if and only if $n < 11$ or
$n \in \{13, 16, 992\}$; in other words, except for $25, 31, 1983$, any odd integer greater
than $20$ can be written as the sum of a prime congruent to $5 \bmod 6$, a positive power of $2$
and seven times a positive power of $2$.

Answer: false, for n = 716993899 we have a(n) = 0.
See T. Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?,
[arxiv/2608.11941](https://arxiv.org/pdf/2608.11941).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_157225_conjecture_0/Submission/Spec.lean"]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    a n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992 := by
  sorry

end OeisA157225
