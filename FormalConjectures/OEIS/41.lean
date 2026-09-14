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
# No powers as partition numbers

There are no partition numbers $a(k)$ of the form $x^m$, with $x,m$ integers $>1$.

*Reference:* [A41](https://oeis.org/A41)
-/

namespace OeisA41

open Nat

/-- The `n`-th partition number. -/
def a (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by decide +native

@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by decide +native

/--
There are no partition numbers $a(k)$ of the form $x^m$, with $x,m$ integers $>1$.
See comment by Zhi-Wei Sun (Dec 02 2013).
-/
@[category research open, AMS 11]
theorem noPowerPartitionNumber : answer(sorry) ↔ ∀ k, ¬IsPerfectPower (a k) := by
  sorry

end OeisA41
