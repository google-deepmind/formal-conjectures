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
A233566: $a(n) = \left|\{0 < p < n: p \text{ and } p \cdot \phi(n-p) - 1 \text{ are both prime}\}\right|$,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p => Nat.Prime p ∧ Nat.Prime (p * Nat.totient (n - p) - 1)) (Finset.range n))

/--
Conjecture: $a(n) > 0$ for all $n > 3$. Also, for any $n > 2$ there is a prime $p < n$ with $p^2 \cdot \phi(n-p) - 1$ prime.
-/
theorem oeis_233566_conjecture_0 :
  (∀ n, 3 < n → a n > 0) ∧
  (∀ n, 2 < n → ∃ p, p < n ∧ Nat.Prime p ∧ Nat.Prime (p ^ 2 * Nat.totient (n - p) - 1)) := by
  sorry
