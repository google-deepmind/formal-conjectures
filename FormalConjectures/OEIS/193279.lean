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
module

public import FormalConjecturesUtil

/-!
# Number of distinct sums of distinct proper divisors of $n$

The sequence $a(n)$ counts the number of distinct sums of non-empty subsets of the proper divisors
of $n$.

*References:*
- [A193279](https://oeis.org/A193279)
-/

@[expose] public section

namespace OeisA193279

/--
Number of distinct sums of distinct proper divisors of $n$ (excluding the empty sum $0$).
-/
def a (n : ℕ) : ℕ :=
  (n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x)).card - 1

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by decide

/--
If $n$ is an even perfect number, then $a(n) = n$.
- _Michael Engling_, Jul 20 2011
-/
@[category textbook, AMS 11]
theorem a_eq_self_of_perfect_of_even (n : ℕ) (hperf : n.Perfect) (heven : Even n) :
    a n = n := by
  sorry

/--
Is the converse true, i.e., if $a(n) = n$, is $n$ necessarily an even perfect number?
- _Michael Engling_, Jul 20 2011

The answer is no: for example, $n = 492 = 2^2 \cdot 3 \cdot 41$ and
$n = 1652 = 2^2 \cdot 7 \cdot 59$ satisfy $a(n) = n$ but are abundant rather than perfect.
-/
@[category research solved, question, AMS 11]
theorem conjecture : ¬ ∀ n : ℕ, 0 < n → a n = n → n.Perfect ∧ Even n := by
  sorry

end OeisA193279
