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

open Nat List

/--
A340592: $a(n)$ is the concatenation of the prime factors (with multiplicity) of $n$ modulo $n$.
The prime factors are taken in non-decreasing order as given by $n.\operatorname{primeFactorsList}$.
-/
def a (n : ℕ) : ℕ :=
  if n < 2 then 0
  else
    let factors_list := n.primeFactorsList

    -- Calculates 10^(number of decimal digits of k)
    let pow10_len (k : ℕ) : ℕ := 10 ^ (Nat.digits 10 k).length

    -- The concatenation operation: acc || factor
    let concat_op (acc factor : ℕ) : ℕ :=
      acc * pow10_len factor + factor

    (factors_list.foldl concat_op 0) % n

theorem a_two : a 2 = 0 := by
  norm_num[a]

theorem a_three : a 3 = 0 := by
  (inhabit Int)
  simp_all[a]

theorem a_four : a 4 = 2 := by
  simp_all[a]

theorem a_five : a 5 = 0 := by
  norm_num[a]
  norm_num [Nat.primeFactorsList]

/-- The property of being composite (n > 1 and not prime) -/
def Nat.composite (n : ℕ) : Prop := ¬ (Nat.Prime n) ∧ 1 < n

/--
The first composite n for which a(n)=0 is 28749. Are there others?
-/
theorem oeis_340592_conjecture_0 :
  (Nat.composite 28749 ∧ a 28749 = 0) ∧
  (∀ n : ℕ, Nat.composite n ∧ n < 28749 → a n ≠ 0) :=
by sorry
