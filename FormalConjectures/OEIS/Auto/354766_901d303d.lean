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

open Int Finset
open scoped BigOperators

/-- The number of integral pairs $(h, i)$ such that $h+i = a$ and $h^2+i^2 = b$. -/
private def count_solutions_pair (a b : ℤ) : ℕ :=
  let v : ℤ := 2 * b - a * a
  if v < 0 then 0
  else
    let s := v.sqrt
    if s * s = v then
      if v = 0 then 1
      else 2
    else 0

/-- The number of integral triples $(h, i, j)$ such that $h+i+j = x$ and $h^2+i^2+j^2 = y$. -/
private noncomputable def count_solutions_triple (x y : ℤ) : ℕ :=
  if y < 0 then 0
  else if x * x > 3 * y then 0
  else
    let m : ℤ := y.sqrt
    Finset.Icc (-m) m |>.sum fun c => count_solutions_pair (x - c) (y - c * c)

/--
A354766: $1/4$ of the total number of integral quadruples $(h, i, j, k)$
with sum $h+i+j+k = n$ and sum of squares $h^2+i^2+j^2+k^2 = n^2$.
The formalization follows Robert Israel's approach of successive reduction to bivariate Diophantine equations.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_int : ℤ := n
    let n_sq : ℤ := n_int * n_int

    -- The fourth variable $k=d$ ranges in $[-n, n]$.
    let m_d : ℤ := n_int
    let range_d : Finset ℤ := Finset.Icc (-m_d) m_d

    let total_solutions : ℕ := range_d.sum fun d => count_solutions_triple (n_int - d) (n_sq - d * d)

    total_solutions / 4


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 4 := by
  sorry

theorem a_four : a 4 = 2 := by
  sorry

open Nat
open scoped Nat

/--
Conjecture 1 from Colin Mallows: tq/4 (the sequence a(n)) is a multiplicative sequence.
A sequence $f : \mathbb{N} \to \mathbb{N}$ is multiplicative if $f(1) = 1$ and for all coprime $m, n$, we have $f(m \cdot n) = f(m) \cdot f(n)$.
-/
theorem oeis_354766_conjecture_1_multiplicative :
  a 1 = 1 ∧ (∀ {m n : ℕ}, m.Coprime n → a (m * n) = a m * a n) :=
  by sorry

/--
A354766 Conjecture 2 (partially formalized): When $n = p^k$, $p$ prime and $k \ge 1$, the explicit formulas for $tq(n)/4 = a(n)$ hold.
We clear denominators to keep the statement within ℕ arithmetic whenever possible.
-/
theorem oeis_354766_conjecture_2_on_a_of_prime_power :
  ∀ (p : ℕ) (k : ℕ), p.Prime → 1 ≤ k →
  let n := p ^ k
  (p = 2 ∧ k = 1 → a n = 2) ∧
  (p = 2 ∧ 2 ≤ k → a n = 2) ∧
  (p = 3 → a n = (3 * n - 1) / 2) ∧
  -- Case p ≡ 5 (mod 6): a(n) = n + 2*(n-1)/(p-1)
  -- formalized as: a(n)*(p-1) = n*(p-1) + 2*(n-1)
  (p % 6 = 5 → a n * (p - 1) = n * (p - 1) + 2 * (n - 1)) ∧
  (p % 6 = 1 → a n = n) :=
  by sorry
