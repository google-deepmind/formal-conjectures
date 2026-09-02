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
# Sum of fourth powers of Fibonacci-like binomial coefficients

The sequence is defined by
$$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4.$$

*References:*
- [A181546](https://oeis.org/A181546)-/

namespace OeisA181546

open Filter Real

/-- The generalized sum $F(n, L) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^L$. -/
def F (n L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k) ^ L

/-- $a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4$. -/
def a (n : ℕ) : ℕ := F n 4

/-- Lucas numbers $L(0) = 2, L(1) = 1, L(n) = L(n-1) + L(n-2)$. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Conjectured limit value for $F(n+1, L) / F(n, L)$. -/
noncomputable def limitValue (L : ℕ) : ℝ :=
  (Nat.fib L * sqrt 5 + lucas L) / 2

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 17 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 83 := by decide

/--
Conjecture: Given $F(n,L) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^L$, then
$\lim_{n\to\infty} F(n+1,L)/F(n,L) = (\mathrm{Fibonacci}(L)\sqrt{5} + \mathrm{Lucas}(L))/2$ for
$L \ge 0$ where $\mathrm{Fibonacci}(n) = \mathrm{A000045}(n)$ and
$\mathrm{Lucas}(n) = \mathrm{A000032}(n)$.-/
@[category research open, AMS 11]
theorem conjecture (L : ℕ) :
    Tendsto (fun n => (F (n + 1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limitValue L)) := by
  sorry

end OeisA181546
