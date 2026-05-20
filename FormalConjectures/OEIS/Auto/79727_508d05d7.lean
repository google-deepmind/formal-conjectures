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
A079727: $a(n) = 1 + \binom{2}{1}^3 + \binom{4}{2}^3 + \cdots + \binom{2n}{n}^3$.
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^3$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k : ℕ => (Nat.choose (2 * k) k) ^ 3)


theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 9 := by sorry
theorem a_two : a 2 = 225 := by sorry
theorem a_three : a 3 = 8225 := by sorry


/--
A003625: Primes $p$ such that $p \equiv 3, 5, 7, \text{ or } 13 \pmod{14}$.
This set of primes is relevant to the conjectures on A079727.
-/
def IsInA003625 (p : ℕ) : Prop :=
  Nat.Prime p ∧ (p % 14 = 3 ∨ p % 14 = 5 ∨ p % 14 = 7 ∨ p % 14 = 13)

/--
Conjecture 2 from A079727 (Peter Bala's Conjectures):
If prime p is in A003625 then a(p*(p-1)) == p^2 (mod p^3).
-/
theorem oeis_79727_conjecture_2 {p : ℕ} (h_prime_in_A003625 : IsInA003625 p) :
  a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  sorry
