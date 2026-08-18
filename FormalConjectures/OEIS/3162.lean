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
# A binomial coefficient summation

A binomial coefficient summation: $a(n) = S(3, n) / S(1, n)$, where for a positive integer $r$
we define
$$S(r,n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^r$$
with $\binom{n}{-1} = 0$.

*References:*
- [A003162](https://oeis.org/A003162)
- H. W. Gould, Problem E2384, Amer. Math. Monthly, 81 (1974), 170-171
-/

namespace OeisA3162

/-- A binomial coefficient summation: $a(n) = S(3, n) / S(1, n)$. -/
def a (n : ℕ) : ℚ :=
  let numerator : ℚ := ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℚ := (n.choose k : ℚ) - (if k = 0 then 0 else (n.choose (k - 1) : ℚ))
    diff ^ 3
  let denominator : ℚ := (n.choose (n / 2) : ℚ)
  numerator / denominator

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℚ :=
  a (2 * n - 1)

macro "eval_a" : tactic =>
  `(tactic| (dsimp [a]
             norm_num [Finset.sum_range_succ, Nat.choose_succ_succ, Nat.choose_zero_succ]))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by eval_a

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by eval_a

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by eval_a

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by eval_a

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by eval_a

/--
$a(n)$ is an integer for all $n \ge 0$.
- Solution to Problem E2384 by H. W. Gould, Amer. Math. Monthly, 81 (1974), 170-171
-/
@[category textbook, AMS 11]
theorem a_is_integer (n : ℕ) : (a n).den = 1 := by
  sorry

/--
Let $b(n) = a(2n-1)$. Then the supercongruence $b(n p^k) \equiv b(n p^{k-1}) \pmod{p^{3k}}$
holds for positive integers $n$ and $k$ and all primes $p \ge 5$.
- Zhi-Wei Sun, Nov 16 2019
-/
@[category research open, AMS 11]
theorem conjecture (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (b (n * p ^ k)).num ≡ (b (n * p ^ (k - 1))).num [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OeisA3162
