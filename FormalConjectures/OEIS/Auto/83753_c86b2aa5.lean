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

open Nat Set List
open scoped Classical

/--
A083753: Smallest palindromic number with exactly $n$ divisors, or 0 if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let is_palindrome (m : ℕ) : Prop := Nat.digits 10 m = (Nat.digits 10 m).reverse

  -- The number of divisors of m.
  let tau (m : ℕ) : ℕ := Finset.card (Nat.divisors m)

  -- The set of positive natural numbers $m$ that are palindromes and have n divisors.
  let S : Set ℕ := {m : ℕ | m > 0 ∧ is_palindrome m ∧ tau m = n}

  -- Since Nat.sInf returns the smallest element of a set if non-empty, and 0 if empty,
  -- we can use an if statement to formally satisfy the "or 0 if no such number exists" clause.
  if h : S.Nonempty then
    sInf S
  else
    0

theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 2 := by sorry
theorem a_three : a 3 = 4 := by sorry
theorem a_four : a 4 = 6 := by sorry


/--
A conjecture often cited in connection with A083753:
There are no palindromic numbers greater than 1 which are the fifth or higher power of a natural number.
This implies that a(n)=0 for certain values of n (like 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
because the only numbers with these prime numbers of divisors are high perfect powers.
-/
theorem oeis_83753_conjecture_0 :
  ∀ (m k : ℕ),
    m > 1 ∧
    (Nat.digits 10 m = (Nat.digits 10 m).reverse) ∧
    k ≥ 5 ∧
    (∃ x : ℕ, m = x ^ k)
    →
    False
:= by sorry
