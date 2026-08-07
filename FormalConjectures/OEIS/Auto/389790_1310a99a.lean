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
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  -- Iterate over pairs (p, q) from R x R
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-- The statement that $n_{max}$ is the conjectured largest value of $n$ such that $a(n) = k$. -/
def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

/--
  A389790 Conjecture: a(n) = k for a largest value of n given by the table below.

  k     conjectured largest value of n for which a(n) = k
----------------
  2      833
  3     1487
  4     1411
  5     1523
  6     1747
  7     2621
  8     2153
  9     3091
  10     3238
-/
theorem oeis_A389790_conjecture_max_n :
  is_conjectured_largest_value 833 2 ∧
  is_conjectured_largest_value 1487 3 ∧
  is_conjectured_largest_value 1411 4 ∧
  is_conjectured_largest_value 1523 5 ∧
  is_conjectured_largest_value 1747 6 ∧
  is_conjectured_largest_value 2621 7 ∧
  is_conjectured_largest_value 2153 8 ∧
  is_conjectured_largest_value 3091 9 ∧
  is_conjectured_largest_value 3238 10
:= by sorry
