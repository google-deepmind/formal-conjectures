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

open Nat Finset BigOperators Int

-- Generalized binomial coefficient $\binom{r}{k}$ for $r \in \mathbb{Z}, k \in \mathbb{N}$.
-- We use the definition $\binom{r}{k} = \frac{\prod_{i=0}^{k-1} (r-i)}{k!}$ and rely on
-- the known property that this division results in an integer.
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

-- Helper definition for the generalized coefficient formula.
/--
The $k$-th power series coefficient of $c(x)^r$: $\frac{r}{r+k}\binom{r+2k-1}{k}$.
This expression is known to be an integer for all $r \in \mathbb{Z}$.
-/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    -- The division is exact because the coefficient is an integer.
    -- We rely on integer division to compute the result.
    (r * num_choose) / denominator

/--
The generalized sequence $a_m(n)$ is the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{m \cdot n}$ evaluated at $x=1$.
$$a_m(n) = \sum_{k=0}^n [x^k] c(x)^{m n}$$
-/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator

/--
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  sorry
