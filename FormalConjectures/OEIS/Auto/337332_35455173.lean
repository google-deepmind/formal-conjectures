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

open Finset Nat

/--
A337332: $a(n) = \sum_{k=0}^n \binom{n}{k}\binom{n+k}{k}\binom{2k}{k}\binom{2n-2k}{n-k}(-8)^{n-k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    -- Nat.centralBinom m = (2 * m).choose m which is C(2(n-k), n-k)
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = -12 := by
  delta a
  norm_cast at *

theorem a_two : a 2 = 228 := by
  rfl

theorem a_three : a 3 = -3504 := by
  rfl

-- The sum in the conjecture is $S(n) = \sum_{k=0}^{n-1} (-1)^k (4k+1) 48^{n-1-k} a(k)$.
def conjecture_sum (n : ℕ) : ℤ :=
  Finset.sum (range n) fun k =>
    let k_int : ℤ := k;
    -- Since k < n, n - 1 - k is a valid natural number exponent.
    let exp : ℕ := n - 1 - k;
    (-1 : ℤ) ^ k * (4 * k_int + 1) * (48 : ℤ) ^ exp * a k

/--
oeis_337332_conjecture_2: Conjecture 2: For each n > 0, the number (Sum_{k=0..n-1} (-1)^k*(4k+1)*48^(n-1-k)*a(k))/n is a positive integer.
This means:
1. The `conjecture_sum n` is divisible by `n`.
2. The quotient `conjecture_sum n / n` is positive.
-/
theorem oeis_337332_conjecture_2 (n : ℕ) (hn : n > 0) :
    ∃ q : ℤ, (n : ℤ) * q = conjecture_sum n ∧ q > 0 := by
  sorry
