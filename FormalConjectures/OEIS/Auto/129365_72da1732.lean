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
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_A: a(n) is always an integer.
This is formalized as the denominator dividing the numerator for all positive n.
-/
theorem oeis_a129365_conjecture_A (n : ℕ) (hn : 0 < n) :
  ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k) ∣ ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k) := by
  sorry

/--
oeis_a129365_conjecture_B: If p is a prime then p|a(n) if and only if p <= n/3.
Note: Since `a n` is non-zero for $n > 0$, $p \mid a n$ iff $p$ is in the factorization of $a n$.
-/
theorem oeis_a129365_conjecture_B (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  p ∣ a n ↔ p ≤ n / 3 := by
  sorry

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  sorry

/--
oeis_a129365_conjecture_D: Let b(n) = A004125(n). Then
ordp(a(n*p),p) = b(n) + b(floor(n/p)) + b(floor(n/p^2)) + b(floor(n/p^3)) + ....
-/
theorem oeis_a129365_conjecture_D (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  (a (n * p)).factorization p = ∑' (i : ℕ), b (n / (p ^ i)) := by
  sorry
