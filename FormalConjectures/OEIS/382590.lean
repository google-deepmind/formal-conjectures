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
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
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
The k-th prime factor of an integer n (where k>=1), counted with multiplicity.
This is defined as the k-th element (0-indexed k-1) of `Nat.primeFactorsList n.natAbs`.
Returns 1 if n has fewer than k prime factors or if n is 0, 1, or -1,
following the informal convention.
-/
def kthPrimeFactor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let n_abs := Int.natAbs n
  let L := primeFactorsList n_abs
  -- prime factors list length is L.length. We look for k-th element, index k-1.
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

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/382590.wip.lean#L281"]
theorem kthPrimeFactor_periodic : ∀ k : ℕ, k ≥ 2 → ∃ N₀ p : ℕ, p > 0 ∧
    ∀ n : ℕ, n ≥ N₀ → kthPrimeFactor k (a (n + p)) = kthPrimeFactor k (a n) := by
    sorry

end OeisA382590
