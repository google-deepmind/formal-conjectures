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
A277060: The sequence $a(n)$ is defined by
$$a(n) = \frac{1}{2} \sum_{k=0}^n \left( \binom{n}{k} \binom{n+k}{k+1} \right)^2 \quad \text{for } n \ge 0$$
-/
def A277060 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) / 2


theorem a_zero : A277060 0 = 0 := by sorry

theorem a_one : A277060 1 = 1 := by sorry

theorem a_two : A277060 2 = 28 := by sorry

theorem a_three : A277060 3 = 729 := by sorry


/--
Conjecture: the supercongruences a(p-1) == 1 (mod p^4) holds for all primes p >= 5 and
a(p^2-1) == 1 (mod p^5) holds for all primes p >= 3. - Peter Bala, Mar 22 2023
-/
theorem oeis_277060_conjecture_0 :
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p → A277060 (p - 1) ≡ 1 [MOD p ^ 4]) ∧
  (∀ p : ℕ, Nat.Prime p → 3 ≤ p → A277060 (p ^ 2 - 1) ≡ 1 [MOD p ^ 5]) := by sorry
