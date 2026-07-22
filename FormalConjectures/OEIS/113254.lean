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
# Corresponds to m = 8 in a family of 4th-order linear recurrence sequences

This sequence is defined by the linear recurrence relation
a(n) = -4 a(n-1) + 256 a(n-3) + 4096 a(n-4) for n > 3.
Initial values are a(0) = -1, a(1) = 4, a(2) = 176, a(3) = 3136.

*References:*
- [A113254](https://oeis.org/A113254)
-/

namespace OeisA113254

/-- a n is the sequence defined by the linear recurrence a(n) = -4 a(n-1) + 256 a(n-3) + 4096 a(n-4)
with initial values -1, 4, 176, 3136. -/
def a : ℕ → ℤ
| 0 => -1
| 1 => 4
| 2 => 176
| 3 => 3136
| n + 4 => -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n

@[category test, AMS 11]
lemma test_a_0 : a 0 = -1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 176 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 3136 := by rfl

@[category test, AMS 11]
lemma test_a_4 : a 4 = -15616 := by rfl

/--
Conjecture: a(m, 2*n+1) is a perfect square for all m, n (see A113249).
Specialized for m=8, which is A113254.
-/
@[category research open, AMS 11]
theorem main_conjecture : ∀ n : ℕ, ∃ k : ℤ, a (2 * n + 1) = k ^ 2 := by
  sorry

end OeisA113254
