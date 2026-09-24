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
# Equal prime counts in adjacent intervals $(kn, (k+1)n)$ and $((k+1)n, (k+2)n)$

Let $\pi$ denote the prime counting function. The sequence $a(n)$ counts the number of integers
$0 < k < n$ such that the intervals $(kn, (k+1)n)$ and $((k+1)n, (k+2)n)$ contain the same number
of primes.

*References:*
- [A238281](https://oeis.org/A238281)
-/

namespace OeisA238281

/-- $a(n)$ is the number of integers $0 < k < n$ such that the two intervals $(kn, (k+1)n)$ and
$((k+1)n, (k+2)n)$ contain the same number of primes. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    if Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) =
       Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

/--
Conjecture: Moreover, if $n > 1$ is not equal to $8$, then there is a positive integer $k < n$ with
$2k + 1$ prime such that the two intervals $((k-1)n, kn]$ and $(kn, (k+1)n]$ contain the same
number of primes.

OEIS states open intervals, but for $n = 2$ the only candidate is $k = 1$, where the open
interval $(0, 2)$ contains 0 primes while $(2, 4)$ contains 1 prime. Half-open intervals
$((k-1)n, kn]$ match Sun's Mathematica formula `PrimePi[k*n] - PrimePi[(k-1)*n]` and hold for
$n = 2$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 1 < n) (h8 : n ≠ 8) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (2 * k + 1).Prime ∧
      Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n) =
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) := by
  sorry

/--
Conjecture (ii): For any integer $n > 4$, there is a positive integer $k < p_n$ such that all the
three intervals $(kn, (k+1)n)$, $((k+1)n, (k+2)n)$, $((k+2)n, (k+3)n)$ contain the same number of
primes, i.e., $\pi(kn)$, $\pi((k+1)n)$, $\pi((k+2)n)$, $\pi((k+3)n)$ form a $4$-term arithmetic
progression.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 4 < n) :
    ∃ k : ℕ, 0 < k ∧ k < Nat.nth Nat.Prime (n - 1) ∧
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) =
      Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) ∧
      Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) =
      Nat.primeCounting ((k + 3) * n) - Nat.primeCounting ((k + 2) * n) := by
  sorry

end OeisA238281
