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

/--
A185150: Number of odd primes $p$ between $n^2$ and $(n+1)^2$ with $\left(\frac{n}{p}\right) = 1$, where $\left(\frac{\cdot}{\cdot}\right)$ is the Legendre symbol.
We use Jacobi symbol, which equals the Legendre symbol when the modulus $p$ is prime.
-/
def a (n : ℕ) : ℕ :=
  -- Filter the set of natural numbers in the open interval $(n^2, (n+1)^2)$
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧ -- p is an odd prime
    jacobiSym (n : ℤ) p = 1
  ) |>.card


/-- Conjecture: a(n)>0 for all n>0. -/
theorem oeis_a185150_conjecture_1 : ∀ (n : ℕ), 0 < n → 0 < a n := by sorry

/-- We have verified the conjecture for n up to 10^9. -/
theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by sorry
