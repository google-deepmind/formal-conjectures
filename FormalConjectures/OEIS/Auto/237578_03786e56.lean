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

open scoped Nat.Prime

/--
A237578: $a(n) = |\left\{0 < k < n: \pi(k \cdot n) \text{ is prime}\right\}|$, where $\pi(\cdot)$ is the prime counting function (A000720).
-/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

/--
Conjecture: a(n) > 0 for all n > 2, and a(n) = 1 only for n = 5, 8, 13.
Moreover, for each n = 1, 2, 3, ..., there is a positive integer k < 3*sqrt(n) + 3 with pi(k*n) prime.
-/
theorem oeis_237578_conjecture_0 :
  -- Part 1: a(n) > 0 for all n > 2
  (∀ n : ℕ, 2 < n → a n > 0) ∧
  -- Part 2: a(n) = 1 only for n = 5, 8, 13
  (∀ n : ℕ, a n = 1 ↔ n = 5 ∨ n = 8 ∨ n = 13) ∧
  -- Part 3: k < 3*sqrt(n) + 3 with pi(k*n) prime
  (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) :=
by sorry
