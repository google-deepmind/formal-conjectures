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

/--
A250131: $a(n)$ is the odd part of the digital sum of $3^n$ divided by the maximal possible power of $3$.
The sequence is defined by the formula derived from the PARI code:
$$a(n) = \frac{S(3^n)}{3^{\nu_3(S(3^n))} \cdot 2^{\nu_2(S(3^n))}}$$
where $S(m)$ is the sum of base 10 digits of $m$, and $\nu_p(m)$ is the $\mathrm{p}$-adic valuation of $m$.
-/
def a (n : ℕ) : ℕ :=
  let d := List.sum (Nat.digits 10 (3 ^ n))
  let v3 := padicValNat 3 d
  let v2 := padicValNat 2 d
  d / (3 ^ v3 * 2 ^ v2)

/-- Sequence b(n) related to A250131: b(1)=2, b(2)=3, and for n>=3, b(n)=a(n-2). -/
def b (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | n' + 3 => a (n' + 1)

/-- The set of indices $n \ge 1$ such that $b(n) \ne 1$ and $b(n)$ is not a multiple of any $b(k)$ for $1 \le k < n$ where $b(k) \ne 1$.
This formalizes the "Eratosthenes-like sieve" on the sequence b(n) after removing 1's, by insisting that a term must not be divisible by any preceding non-one term. -/
def sieved_indices : Set ℕ :=
  { n | 1 ≤ n ∧ b n ≠ 1 ∧ ∀ k, (1 ≤ k ∧ k < n ∧ b k ≠ 1) → ¬ (b k ∣ b n) }

/--
Conjecture A250131: Consider the sequence {b(n)}, such that b(1)=2, b(2)=3, and for n>=3, b(n)=a(n-2).
We conjecture that, if we apply the Eratosthenes-like sieve to b(n) and remove 1's, then we obtain a sequence of primes.
-/
theorem oeis_a250131_conjecture :
    ∀ n : ℕ, n ∈ sieved_indices → Nat.Prime (b n) := by
  sorry
