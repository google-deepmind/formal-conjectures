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

/-!
# A116150

a(n) = sum_{j=1..n} (3^j + (-2)^j).

*References:*
- [A116150](https://oeis.org/A116150)
-/

namespace OeisA116150

open BigOperators

/-- a n is the sum of 3^j + (-2)^j for j from 1 to n. -/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) (fun j : ℕ => (3 : ℤ) ^ j + ((-2) : ℤ) ^ j)).toNat

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 14 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 33 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 130 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 341 := by decide

/--
First primes are a(11)=264353 and a(17)=193622861.
Additional primes: a(71), a(91), a(431).
What is the next prime?
-/
@[category research open, AMS 11]
theorem conjecture1 : answer(sorry) = a (sInf {n : ℕ | 431 < n ∧ Nat.Prime (a n)}) := by
  sorry

end OeisA116150
