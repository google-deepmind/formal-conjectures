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
# Denominator of $B_{n+1}(x) - B_{n+1}$

The sequence $a(n)$ is the least common multiple of the denominators of the coefficients of the
polynomial $B_{n+1}(x) - B_{n+1}$, where $B_m(x) = \sum_{k=0}^m \binom{m}{k} B_{m-k} x^k$ is the
$m$-th Bernoulli polynomial and $B_m$ is the $m$-th Bernoulli number.

*References:*
- [A195441](https://oeis.org/A195441)
- [Finiteness of Bernoulli polynomials](https://arxiv.org/abs/2310.01325)
  by *Bernd C. Kellner*, J. Integer Seq. 27 (2024)
-/

namespace OeisA195441

/--
The least common multiple of the denominators of the coefficients of $B_{n+1}(x) - B_{n+1}$.
Since $B_{n+1}(x) - B_{n+1} = \sum_{k=1}^{n+1} \binom{n+1}{k} B_{n+1-k} x^k$, this is the least
common multiple of the denominators of $\binom{n+1}{k} B_{n+1-k}$ for $1 \le k \le n + 1$.
-/
def a (n : ℕ) : ℕ :=
  let N := n + 1
  (Finset.Icc 1 N).lcm fun k => (((N.choose k : ℚ) * bernoulli (N - k)).den)

/-- The radical $\operatorname{rad}(n)$ is the product of the distinct prime factors of $n$. -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide +native

/--
The equation $a(n-1) = \operatorname{rad}(n+1)$ has only finitely many solutions, where
$\operatorname{rad}(n)$ is the radical of $n$. It is conjectured that
$S = \{3, 5, 8, 9, 11, 27, 29, 35, 59\}$ is the full set of all such solutions.
- _Bernd C. Kellner_, Oct 18 2023
-/
@[category research open, AMS 11]
theorem conjecture :
    {n : ℕ | 1 ≤ n ∧ a (n - 1) = radical (n + 1)} =
      ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ) := by
  sorry

end OeisA195441
