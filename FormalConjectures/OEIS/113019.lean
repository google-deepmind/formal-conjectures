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

import FormalConjecturesUtil

/-!
# Number of digits of n raised to the power of the digital root of n

A113019: (Number of digits of n) raised to the power of (the digital root of n).

*References:*
- [A113019](https://oeis.org/A113019)
-/

namespace OeisA113019

open Nat

/-- 
a n is the (Number of digits of n) raised to the power of (the digital root of n), 
with appropriate adjustments for n=0.
-/
def a (n : ℕ) : ℕ :=
  -- The base: number of digits of n (adjusting n=0 to have 1 digit, like n=1).
  let num_digits : ℕ := (Nat.digits 10 (max 1 n)).length

  -- The exponent: digital root of n. This correctly yields 0 for n=0, and the standard 1..9 for n>0.
  let digital_root : ℕ := if n = 0 then 0 else (n - 1) % 9 + 1

  num_digits ^ digital_root

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
n=1 and 32 are fixed points. Are there any others?
-/
@[category research open, AMS 11]
theorem main_conjecture : answer(sorry) ↔ ∀ n : ℕ, a n = n → n = 1 ∨ n = 32 := by
  sorry

end OeisA113019
