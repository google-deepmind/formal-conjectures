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
# Corresponds to m = 9 in a family of 4th-order linear recurrence sequences

This sequence is defined by the recurrence relation
a(n) = -4 a(n-1) + 324 a(n-3) + 6561 a(n-4) for n > 3.
Initial values are a(0) = -1, a(1) = 4, a(2) = 227, a(3) = 5329.

*References:*
- [A113255](https://oeis.org/A113255)
-/

namespace OeisA113255

/-- a n is the sequence defined by the linear recurrence a(n) = -4 a(n-1) + 324 a(n-3) + 6561 a(n-4)
with initial values -1, 4, 227, 5329. -/
def a : ℕ → ℤ
| 0 => -1
| 1 => 4
| 2 => 227
| 3 => 5329
| n + 4 => -4 * a (n + 3) + 324 * a (n + 1) + 6561 * a n

@[category test, AMS 11]
theorem a_0 : a 0 = -1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 227 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 5329 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = -26581 := by rfl

/--
Conjecture: a(m, 2*n+1) is a perfect square for all m, n (see A113249).
Specialized for m=9, which is A113255.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ n : ℕ, ∃ k : ℤ, a (2 * n + 1) = k ^ 2 := by
  sorry

end OeisA113255
