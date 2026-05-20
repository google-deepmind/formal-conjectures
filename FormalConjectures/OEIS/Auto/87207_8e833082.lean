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
open scoped Nat.Prime

/--
A087207: A binary representation of the primes that divide a number, shown in decimal.
The value $a(n)$ is given by
$$ a(n) = \sum_{p \mid n, p \text{ prime}} 2^{\pi(p) - 1} $$
where $\pi(p) = \mathrm{primeCounting}(p)$ gives the 1-based index of the prime $p$.
The set of distinct prime factors is the support of $n$'s factorization.
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorization n).support.sum fun p =>
    2 ^ (Nat.primeCounting p - 1)

/--
Conjecture: Starting at any n and iterating the map n -> a(n), we will always reach 0 (see A288569).
This conjecture is equivalent to the conjecture that at any n that is neither a prime nor a power of two,
we will eventually hit a prime number (which then becomes a power of two in the next iteration).
If this conjecture is false then sequence A285332 cannot be a permutation of natural numbers.
On the other hand, if the conjecture is true, then A285332 must be a permutation of natural numbers,
because all primes and powers of 2 occur in definite positions in that tree.
This conjecture also implies the conjectures made in A019565 and A285320 that essentially claim that
there are neither finite nor infinite cycles in A019565.
-/
theorem oeis_87207_conjecture_0 :
  ∀ n : ℕ, ∃ k : ℕ, (a^[k]) n = 0 := by
  sorry
