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
# A109908

a(n) = greatest prime of the form k(n-k)-1, or 0 if no such prime exists.

*References:*
- [A109908](https://oeis.org/A109908)
-/

namespace OeisA109908

/--
a(n) = greatest prime of the form k(n-k)-1, or 0 if no such prime exists.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2))
  |>.image (fun k => k * (n - k) - 1)
  |>.filter Nat.Prime
  |>.sup id

@[category test, AMS 11]
lemma test_a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 5 := by decide

/--
Conjecture: a(n) > 0 for n > 3.
-/
@[category research open, AMS 11]
theorem main_conjecture : ∀ n > 3, a n > 0 := by
  sorry

end OeisA109908
