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
open Finset

/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.
-/
def a (N : ℕ) : ℕ :=
  -- The outer sum runs over $n$ from $0$ to $N$.
  (range (N + 1)).sum (fun n =>
    -- The inner sum runs over $k$ from $0$ to $n$.
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      -- We require $R = N - n(k+1) \ge 0$ and $m = n+1$ must divide $R$.
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        -- $j = R / m$.
        let j : ℕ := R / m
        -- The summand is $\binom{n}{k} \binom{n+j}{j}$.
        n.choose k * (n + j).choose j
      else
        0
    )
  )

/-- oeis_325046_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture). -/
theorem a325046_odd_terms_at_k_times_k_plus_1 (N : ℕ) :
  a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) :=
by sorry
