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

open Nat List Finset

/-- The predicate for a number to be a binary palindrome (OEIS A006995), defined to return Bool. -/
def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

/--
A261680: Number of ordered quadruples $(u,v,w,x)$ of binary palindromes (see A006995) with $u+v+w+x=n$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun u =>
    Finset.sum (Finset.range (n - u + 1)) fun v =>
      Finset.sum (Finset.range (n - (u + v) + 1)) fun w =>
        let x := n - (u + v + w)
        if is_binary_palindrome u ∧
           is_binary_palindrome v ∧
           is_binary_palindrome w ∧
           is_binary_palindrome x
        then 1 else 0


theorem a_zero : a 0 = 1 := by
  simp_all[a]
  simp_all[is_binary_palindrome,Finset.filter_singleton]

theorem a_one : a 1 = 4 := by
  push_cast[a]
  simp_all+decide-contextual[is_binary_palindrome,Finset.sum]

theorem a_two : a 2 = 6 := by
  norm_num[a]
  delta is_binary_palindrome
  push_cast+decide[Nat.digits_def',Nat.digits_zero,if_true,Finset.card_filter,Finset.sum_range_succ,if_false]

theorem a_three : a 3 = 8 := by
  norm_num[a]
  delta is_binary_palindrome
  push_cast+decide[Nat.sub_add_eq,Nat.digits_def',Nat.digits_zero,ite_and, Finset.card_filter, Finset.sum_range_succ]

/-- OEIS A261680 Conjecture: a(n)>0: every number is the sum of four binary palindromes. -/
theorem oeis_261680_conjecture_0 (n : ℕ) : a n > 0 := by
  sorry
