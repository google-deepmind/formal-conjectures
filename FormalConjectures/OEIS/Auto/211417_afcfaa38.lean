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
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 77636318760 := by
  rfl

theorem a_two : a 2 = 53837289804317953893960 := by
  rfl

theorem a_three : a 3 = 43880754270176401422739454033276880 := by
  rfl

open Nat Int Finset

-- Helper definition for the set of indices coprime to 30.
def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

/--
It appears that a(n)/(30*n - 1) is integral for all n (checked up to n = 1000).
More generally, for r >= 1, we conjecture that there exists a constant D(r) such that
D(r)*a(n)/Product_{i = 1..r, i coprime to 30} (30*n - i) is integral for all n.
-/
theorem oeis_a211417_conjecture_general (r : ℕ) (hr : r ≥ 1) :
  ∃ (D : ℤ), D ≠ 0 ∧ ∀ (n : ℕ), divisor_product n r ∣ D * (a n : ℤ) := by
  sorry

/--
It appears that a(n)/(30*n - 1) is integral for all n (checked up to n = 1000).
This is the specific case of the general conjecture for r=1 with D(1)=1.
-/
theorem oeis_a211417_conjecture_specific (n : ℕ) :
  (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  sorry
