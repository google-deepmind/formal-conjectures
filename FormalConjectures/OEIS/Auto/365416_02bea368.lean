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
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition


theorem a_one : a 1 = 2 := by
  sorry

theorem a_two : a 2 = 3 := by
  sorry

theorem a_three : a 3 = 4 := by
  sorry

theorem a_four : a 4 = 5 := by
  sorry

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 :=
by sorry
