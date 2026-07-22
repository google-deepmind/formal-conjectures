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
# Corresponds to m = 4 in a family of 4th-order linear recurrence sequences

This sequence is defined by the linear recurrence relation with signature (-4, 0, 64, 256)
and initial values a(0) = -1, a(1) = 4, a(2) = 32, a(3) = 64.
The recurrence is a(n) = -4 a(n-1) + 64 a(n-3) + 256 a(n-4).

*References:*
- [A113250](https://oeis.org/A113250)
-/

namespace OeisA113250

/-- a n is the sequence defined by the linear recurrence a(n) = -4 a(n-1) + 64 a(n-3) + 256 a(n-4)
with initial values -1, 4, 32, 64. -/
def a : ℕ → ℤ
| 0 => -1
| 1 => 4
| 2 => 32
| 3 => 64
| n + 4 => -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n

@[category test, AMS 11]
theorem a_0 : a 0 = -1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 32 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 64 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = -256 := by rfl

/--
Conjecture: a(m, 2*n+1) is a perfect square for all m (see A113249).
Specialized to m = 4, which is A113250.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ n : ℕ, ∃ k : ℤ, a (2 * n + 1) = k ^ 2 := by
  sorry

end OeisA113250
