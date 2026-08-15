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

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

-- Example computations from OEIS, included for completeness
theorem a_zero : a 0 = 1 := rfl
theorem a_one : a 1 = 13 := by rfl
theorem a_two : a 2 = 621 := by rfl
theorem a_three : a 3 = 40864 := by rfl

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by sorry
