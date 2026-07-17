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
# Number of digits of n raised to the power of the sum of the digits of n

A113010: {Number of digits of n} raised to the power of {the sum of the digits of n}.
$$a(n) = (\text{number of digits of } n)^{\text{sum of the digits of } n}$$

*References:*
- [A113010](https://oeis.org/A113010)
-/

namespace OeisA113010

open Nat

/-- 
a n is the {Number of digits of n} raised to the power of {the sum of the digits of n}.
-/
def a (n : ℕ) : ℕ :=
  (List.length (Nat.digits 10 n)) ^ (List.sum (Nat.digits 10 n))

@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 1 := by native_decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 1 := by native_decide

/--
n=1 and 32 are two fixed points. Are there any others?
-/
@[category research open, AMS 11]
theorem main_conjecture : answer(sorry) ↔ ∀ n : ℕ, a n = n ∧ n > 0 → n = 1 ∨ n = 32 := by
  sorry

end OeisA113010
