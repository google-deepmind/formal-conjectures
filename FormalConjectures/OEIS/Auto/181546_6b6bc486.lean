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

/--
A181546: $a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ 4

-- The general function F(n, L) mentioned in the conjecture.
def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

open Filter Asymptotics Real

/--
The conjectured limit value, specialized for a given L.
$T(L) = \frac{\mathrm{Fib}(L)\sqrt{5} + \mathrm{Lucas}(L)}{2}$.
We use `lucasNumber` from $\mathbb{Z}$ and cast to $\mathbb{R}$.
-/
noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

/--
A181546 Conjecture: Given $F(n,L) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^L$,
then $\lim_{n\to\infty} \frac{F(n+1,L)}{F(n,L)} = \frac{\mathrm{Fib}(L)\sqrt{5} + \mathrm{Lucas}(L)}{2}$ for $L \ge 0$.

This requires the sequence $F(n, L)$ to be eventually non-zero, which is true since the terms are positive.
We state the limit for $L \ge 0$, corresponding to $\mathtt{L} : \nat$.
-/
theorem oeis_181546_conjecture_0 (L : ℕ) :
    Tendsto (fun n => (F (n+1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limit_value L)) := by
  sorry
