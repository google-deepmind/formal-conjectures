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

open Nat Finset

/--
A072780: $a(n) = \sigma_2(n) + \phi(n) \sigma(n) - 2n^2$.
-/
def a (n : ℕ) : ℕ :=
  let sigma2_n : ℕ := n.divisors.sum fun d => d ^ 2
  let sigma1_n : ℕ := n.divisors.sum fun d => d
  let phi_n : ℕ := n.totient
  let two_n_sq : ℕ := 2 * n ^ 2

  -- Calculate over ℤ for subtraction correctness, then convert back to ℕ.
  -- This is safe because the conjecture is that a(n) >= 0.
  ((sigma2_n : ℤ) + (phi_n * sigma1_n : ℤ) - (two_n_sq : ℤ)).toNat

/--
Conjecture A072780 (1) and (2):
(1) a(n) >= 0, with equality only when n is prime (or 1).
(2) a(n) = 2 if and only if n is the product of two distinct primes.
The assertion $a(n) \ge 0$ is trivially true since a(n) is defined as a ℕ.
-/
theorem oeis_72780_conjecture (n : ℕ) :
  (a n = 0 ↔ n = 1 ∨ n.Prime) ∧
  (a n = 2 ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) :=
by sorry

/--
Conjecture relating A072780 to twin primes:
Let $n = m^2 - 1$, then $m-1$ and $m+1$ are twin primes if and only if $a(n) = 2$.
We require $m > 1$ for $m^2-1$ to be positive and $m-1$ to be positive.
Since twin primes must be $(3, 5)$ or higher, we will assume $m > 2$.
-/
theorem oeis_72780_twin_prime_conjecture (m : ℕ) (h_m : m > 2) :
  a (m ^ 2 - 1) = 2 ↔ (m - 1).Prime ∧ (m + 1).Prime :=
by sorry

/--
Conjecture relating A072780 to a Goldbach-like statement:
Let $n = m^2 - r^2$, then $m-r$ and $m+r$ are primes that add to $2m$
if and only if $a(n) = 2$.
The condition that they add to $2m$ is automatic. The formal claim is that
$a(n) = 2$ if and only if $n$ is a product of two primes $p$ and $q$ such that their sum is $2m$.
Since $n = (m-r)(m+r)$, this is equivalent to $m-r$ and $m+r$ being prime.
We require $m > r$.
-/
theorem oeis_72780_goldbach_conjecture (m r : ℕ) (h_pos : m > r) :
  a (m ^ 2 - r ^ 2) = 2 ↔ (m - r).Prime ∧ (m + r).Prime :=
by sorry
