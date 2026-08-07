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
A238281: $a(n) = |\left\{0 < k < n: \text{the two intervals } (k \cdot n, (k+1) \cdot n) \text{ and } ((k+1) \cdot n, (k+2) \cdot n) \text{ contain the same number of primes}\right\}|$.
The sequence $a(n)$ counts the number of positive integers $k < n$ such that the number of primes in
$(k \cdot n, (k+1) \cdot n]$ is equal to the number of primes in $((k+1) \cdot n, (k+2) \cdot n]$,
where the number of primes in $(a, b]$ is $\text{Nat.primeCounting } b - \text{Nat.primeCounting } a$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter
    (fun k : ℕ =>
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)) =
      (Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n)))
    (Finset.Ico 1 n)

theorem a_one : a 1 = 0 := by
  rfl

theorem a_two : a 2 = 1 := by
  trivial

theorem a_three : a 3 = 2 := by
  delta a
  push_cast +decide [ Finset.card_filter, Finset.sum_Ico_eq_sum_range, true,Nat.primeCounting, Finset.sum_range_succ]

theorem a_four : a 4 = 1 := by
  rfl

/--
Conjecture: (i) a(n) > 0 for all n > 1. Moreover, if n > 1 is not equal to 8, then there is a positive
integer k < n with 2*k + 1 prime such that the two intervals ((k-1)*n, k*n) and (k*n, (k+1)*n) contain
the same number of primes.
-/
theorem oeis_238281_conjecture_0 (n : ℕ) :
  (n > 1 → a n > 0) ∧
  (n > 1 ∧ n ≠ 8  →
    ∃ k : ℕ,
      0 < k ∧ k < n ∧
      Nat.Prime (2 * k + 1) ∧
      (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)) =
      (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n))) :=
by sorry
