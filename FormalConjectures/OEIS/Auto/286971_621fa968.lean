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

open ArithmeticFunction Nat BigOperators

/--
A286971: Number of ways to write $n$ as a sum of two numbers, one of which is the product of an even number of distinct primes (including 1) (A030229) and another is the product of an odd number of distinct primes (A030059).
This counts ordered pairs $(e, o)$ of positive integers such that $e+o=n$, $\mu(e)=1$, and $\mu(o)=-1$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun e =>
    let o : ℕ := n - e
    -- The values of moebius e and moebius o are compared with Int 1 and Int -1.
    if moebius e = 1 ∧ moebius o = -1 then 1 else 0


theorem a_zero : a 0 = 0 := by
  sorry

theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

/-- A286971 Conjecture: a(n) > 0 for all n > 10. -/
theorem oeis_286971_conjecture_0 :
  ∀ n, 10 < n → a n > 0 := by sorry
