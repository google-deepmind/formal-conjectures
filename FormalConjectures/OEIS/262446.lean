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
# Additive decompositions of $\pi(\frac{n(n+1)}{2} + 1)$

Number of ways to write $\pi(\frac{n(n+1)}{2} + 1) = \pi(\frac{k(k+1)}{2} + 1) +
\pi(\frac{m(m+1)}{2} + 1)$ with $0 < k < m < n$, where $\pi(x)$ is the prime-counting function.

*References:*
- [A262446](https://oeis.org/A262446)
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641)
  by *Zhi-Wei Sun*, arXiv:1402.6641 (2014)
-/

namespace OeisA262446

/-- The auxiliary sequence $b(n) = \pi(\frac{n(n+1)}{2} + 1)$ (A262439). -/
def b (n : ℕ) : ℕ :=
  Nat.primeCounting (n * (n + 1) / 2 + 1)

/--
Number of ways to write $b(n) = b(k) + b(m)$ with $0 < k < m < n$.
-/
def a (n : ℕ) : ℕ :=
  let target := b n
  ∑ k ∈ Finset.Ico 1 n,
    ((Finset.Ico (k + 1) n).filter (fun m => target = b k + b m)).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/-- The set of exceptional integers $n > 3$ for which $a(n) = 1$. -/
def Singletons : Finset ℕ :=
  {4, 6, 11, 21, 54, 253, 325}

/--
Conjecture: $a(n) > 0$ for all $n > 3$, and $a(n) = 1$ only for
$n = 4, 6, 11, 21, 54, 253, 325$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 < n) :
    0 < a n ∧ (a n = 1 ↔ n ∈ Singletons) := by
  sorry

end OeisA262446
