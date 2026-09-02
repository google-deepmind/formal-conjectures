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

open Nat Finset

/--
A067599: Decimal encoding of the prime factorization of $n$: concatenation of prime factors and exponents.
If $n$ has prime factorization $p_1^{e_1} \cdot \ldots \cdot p_r^{e_r}$ with $p_1 < \ldots < p_r$,
then its decimal encoding is $p_1 e_1 \ldots p_r e_r$.
-/
noncomputable def a067599 (n : ℕ) : ℕ :=
  if n ≤ 1 then
    0 -- Sequence conventionally starts at $n=2$.
  else
    -- Helper function to get digits in most-significant-first order.
    let to_digits (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse

    -- 1. Get the distinct prime factors as a sorted list.
    -- `n.factorization.support` is a Finset, and we sort it to get $p_1 < p_2 < \ldots$.
    -- The result of Finset.sort is a List ℕ.
    let sorted_primes : List ℕ := n.factorization.support.sort (· ≤ ·)

    -- 2. Build the list of all concatenated digits by iterating over the sorted primes.
    -- We fold over the list of primes, appending the digits of p and e to the accumulator.
    let all_digits : List ℕ := sorted_primes.foldr
      (fun p acc =>
        let e : ℕ := n.factorization p
        (to_digits p) ++ (to_digits e) ++ acc) []

    -- 3. Convert the list of digits (most-significant-first) back to a number.
    Nat.ofDigits 10 all_digits.reverse


theorem a_two : a067599 2 = 21 := by
  norm_num[a067599]
  norm_num [ Finsupp.support_single_ne_zero, false,Nat.ofDigits]

theorem a_three : a067599 3 = 31 := by
  delta a067599
  norm_num[Nat.ofDigits,Nat.factorization]

theorem a_four : a067599 4 = 22 := by
  norm_num[a067599]
  norm_num+decide[Nat.primeFactors,←(4).primeFactorsList_count_eq,Nat.primeFactorsList]

theorem a_five : a067599 5 = 51 := by
  norm_num[ a067599]
  norm_num+decide[ Finsupp.support_single_ne_zero]

/-- Is there any solution to a(n) = n? - _Franklin T. Adams-Watters_, Dec 18 2006 -/
theorem oeis_67599_conjecture_0 : ∃ n, 2 ≤ n ∧ a067599 n = n := by
  sorry
