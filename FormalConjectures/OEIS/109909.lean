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
# A109909

a(n) = number of primes of the form k*(n-k)-1.

*References:*
- [A109909](https://oeis.org/A109909)
-/

namespace OeisA109909

/--
a(n) is the number of primes of the form k*(n-k)-1.
This counts the number of distinct prime values in the set {k*(n-k)-1 | 1 <= k < n}.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).image (fun k => k * (n - k) - 1)
  |>.filter Nat.Prime
  |>.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture: a(n) > 0 for n > 3.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ n > 3, a n > 0 := by
  sorry

end OeisA109909
