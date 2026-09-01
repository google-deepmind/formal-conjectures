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
# $a(n) = \operatorname{lcm}\{1,2,\dots,n\}/\operatorname{denom}(H(n))$

*References:*
- [A110566](https://oeis.org/A110566)
-/

namespace OeisA110566

open Nat Finset Rat

/--
The primary defining sequence `a`.
$a(n) = \frac{\operatorname{lcm}_{k=1}^n k}{\operatorname{den}(H_n)}$
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).lcm id / (harmonic n).den

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

@[category test, AMS 11]
theorem a_6 : a 6 = 3 := by native_decide



/--
It is conjectured that every odd number occurs in this sequence.
-/
@[category research open, AMS 11]
theorem conjecture :
  ∀ m : ℕ, Odd m → ∃ n > 0, a n = m := by
  sorry

end OeisA110566
