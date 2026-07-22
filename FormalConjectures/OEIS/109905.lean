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
# A109905

a(n) is the greatest prime of the form k*(n-k)+1, where k can take values from 1 to floor(n/2). a(n)=0 if no such prime exists.

*References:*
- [A109905](https://oeis.org/A109905)
-/

namespace OeisA109905

/--
a(n) is the greatest prime of the form k*(n-k)+1, where k can take values from 1 to floor(n/2).
a(n) = 0 if no such prime exists.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2))
  |>.image (fun k => k * (n - k) + 1)
  |>.filter Nat.Prime
  |>.sup id

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by decide

/--
a(n)=0 for n = 1, 6, 30 and 54. Are there any others?
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) ↔ {n : ℕ | n > 0 ∧ a n = 0} = {1, 6, 30, 54} := by
  sorry

end OeisA109905
