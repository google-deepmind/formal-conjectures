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
# A102847

A102847: $a(0)=1$, $a(n) = a(n-1)^2 + 2$.

*References:*
- [A102847](https://oeis.org/A102847)
-/

namespace OeisA102847

/-- The primary defining sequence `a`.
$a(0)=1$, $a(n) = a(n-1)^2 + 2$. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => (a n) ^ 2 + 2

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 11 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 123 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 15131 := by rfl

/--
Prime for a(1)=3, a(2)=11, a(4)=15131; semiprime for a(3) = 123 = 3 * 41, a(5) = 228947163 = 3 * 76315721.
a(6), added by Jonathan Vos Post, has 4 prime factors. a(7) = 41 * 811^2 * 106693969 * 317171188688357726699 * 8272236925540996054440172449761.
When is the next prime in the sequence?
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) = sInf {n : ℕ | 4 < n ∧ Nat.Prime (a n)} := by
  sorry

end OeisA102847
