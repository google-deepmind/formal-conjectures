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

open Polynomial Finset Nat

/--
A281267: Main diagonal of A276554.
The sequence $a(n)$ is the coefficient of $x^n$ in the polynomial
$$\prod_{k=1}^n (1 - x^k)^{n k}$$
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Polynomial ℤ :=
    (Ico 1 (n + 1)).prod fun k : ℕ =>
      (1 - X ^ k) ^ (n * k)
  P_n.coeff n


theorem a_zero : a 0 = 1 := by
  norm_num[a]

theorem a_one : a 1 = -1 := by
  delta a
  norm_num[Polynomial.coeff_one]

theorem a_two : a 2 = -3 := by
  sorry

theorem a_three : a 3 = 8 := by
  sorry


/--
Conjecture: the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for all primes p >= 3 and all positive integers n and k.
-/
theorem oeis_281267_conjecture_0 (p : ℕ) (n k : ℕ) :
  Nat.Prime p → 3 ≤ p → 1 ≤ n → 1 ≤ k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] :=
by sorry
