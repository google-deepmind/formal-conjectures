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
# Smallest number m such that 2^n - m and 2^n + m are primes

A113213: Smallest number $m$ such that $2^n - m$ and $2^n + m$ are primes.

*References:*
- [A113213](https://oeis.org/A113213)
-/

namespace OeisA113213

open Nat

/-- 
a n is the smallest number m such that 2^n - m and 2^n + m are primes.
Computed by checking elements from 0 to 2^n, as any larger m would make 2^n - m = 0 which is not prime.
-/
def a (n : ℕ) : ℕ :=
  let S := (List.range (2^n + 1)).filter (fun m => (2^n - m).Prime ∧ (2^n + m).Prime)
  S.headD 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by native_decide

/--
Conjecture: a(n) = O(n^3).
-/
@[category research open, AMS 11]
theorem conjecture :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => (n ^ 3 : ℝ)) := by
  sorry

end OeisA113213
