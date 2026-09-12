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
# Periodicity of $k$-th prime factors in coupled nonlinear recurrence $a(n)$

The sequence $a(n)$ is defined by $a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
where $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$, with $a(1)=1, a(2)=2, b(1)=1, b(2)=0$.

*References:*
- [A382590](https://oeis.org/A382590)
- [mathoverflow/490330](https://mathoverflow.net/questions/490330): B. Morga, "Peculiar family of
  recurrence formula where for $n>1$ if you take the $n$-th prime factor of each term, you get an
  eventually periodic sequence", Mar. 31, 2025.
-/

namespace OeisA382590


open Int

/--
Helper function for a, computing the pair $(a(n), b(n))$ such that:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
$b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
-/
def abPair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := abPair (n + 1)
  let (a_n, b_n) := abPair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
The sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and $a(1) = 2$.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def a (n : ℕ) : ℤ := (abPair n).fst

open Nat

/--
The $k$-th smallest distinct prime factor of an integer $n$ (where $k \ge 1$).
This is defined as the $k$-th element (0-indexed $k-1$) of the increasing list of
distinct prime factors of `n.natAbs`.
Returns 1 if n has fewer than k distinct prime factors or if n is 0, 1, or -1,
following the informal convention.
-/
def kthPrimeFactor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let L := n.natAbs.primeFactors.sort (· ≤ ·)
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]


@[category test, AMS 11]
lemma a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_1 : a 1 = 2 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 8 := by rfl


/--
Conjecture: For any $k > 1$, if you take the $k$-th prime factor of each term, you get an eventually periodic sequence. - _Pontus von Brömssen_, Mar 30 2025

Here the $k$-th prime factor of $a(n)$ is the $k$-th smallest distinct prime divisor of
$|a(n)|$; for example the second prime factors of $a(5) = 18$, $a(6) = 20$ and $a(7) = 896$
are $3$, $5$ and $7$.

This was proved by Terence Tao in a [MathOverflow answer](https://mathoverflow.net/a/490348),
using that $a(n)$ divides $a(n+3)$ for all $n$.
-/
@[category research solved, AMS 11]
theorem kthPrimeFactor_periodic : ∀ k : ℕ, k ≥ 2 → ∃ N₀ p : ℕ, p > 0 ∧
    ∀ n : ℕ, n ≥ N₀ → kthPrimeFactor k (a (n + p)) = kthPrimeFactor k (a n) := by
    sorry

end OeisA382590
