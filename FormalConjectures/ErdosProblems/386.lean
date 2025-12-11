/-
Copyright 2025 The Formal Conjectures Authors.

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
--open Nat
/-!
# Erdős Problem 386

*References:*
- [erdosproblems.com/386](https://www.erdosproblems.com/386)
-/

namespace Erdos386

/-
S is a finite set of consecutive primes:
-/
def ConsecutivePrimes (S : Finset ℕ) (l : ℕ) : Prop :=
    ∃ a, Nat.card S = l ∧ S = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}
/-

Erdos 386 Conjecture:
Are there infinitely many integers n and k, such that the binomial coefficient of n and k is the
product of consecutive prime numbers; i.e.,
\[ {n}\choose{k} = \prod_{p \in P} p \] ?,
where P is a set of consecutive prime numbers.


A solution to Erdos' 386 is a tuple `(n, k, P)`, where `n` and `k` are integers and `P`
is a non-empty finite set of distinct prime numbers, such that it's product is
the binomial coefficient n choose k.
Moreover `n` and `k` satisfy `2 ≤ k`, `k ≤ n - 2`.
-/
def erdos_386_solutions : Set (ℕ × ℕ × Finset ℕ) := {
  (n, k, P) |
    (2 ≤ k ∧ k ≤ n - 2) ∧
    P.Nonempty ∧
    ConsecutivePrimes P P.card ∧
    Nat.choose n k = ∏ p ∈ P, p
  }
/--

Here is the formalisation of Erdos 386 problem:
-/
@[category research open, AMS 11]
theorem erdos_386_conjecture : erdos_386_solutions.Infinite ↔ answer(sorry) := by
  sorry

end Erdos386
