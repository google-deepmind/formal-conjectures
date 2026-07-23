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

open Nat Int Finset

/-- The auxiliary integer sequence $F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$, corresponding to OEIS A024168. -/
def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    -- Term is $\frac{n!}{k} (-1)^{k}$.
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

/--
A335023: Ratios of consecutive terms of A334958.
$$a(n) = \frac{A334958(n+1)}{A334958(n)}$$
where $A334958(m) = \gcd(F(m+1), F(m))$.
-/
def a (n : ℕ) : ℕ :=
  let A334958 (m : ℕ) : ℕ := Int.gcd (F_aux (m + 1)) (F_aux m)

  let g_n := A334958 n
  let g_n_plus_1 := A334958 (n + 1)

  -- A334958(n) is non-zero for $n \ge 1$.
  if g_n = 0 then 0 else g_n_plus_1 / g_n


/-- Conjecture: a(n) = 1 if and only if n+1 is prime. -/
theorem oeis_335023_conjecture_0 (n : ℕ) (h : n > 0) :
  a n = 1 ↔ Nat.Prime (n + 1) := by sorry
