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

import FormalConjectures.Util.ProblemImports

/--
A102847: $a(0)=1$, $a(n) = a(n-1)^2 + 2$.
-/
def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 3 := by
  rfl

theorem a_two : a 2 = 11 := by
  rfl

theorem a_three : a 3 = 123 := by
  rfl

/--
oeis_102847_conjecture_0: Prime for a(1)=3, a(2)=11, a(4)=15131; semiprime for a(3) = 123 = 3 * 41, a(5) = 228947163 = 3 * 76315721.
a(6), added by Jonathan Vos Post, has 4 prime factors. a(7) = 41 * 811^2 * 106693969 * 317171188688357726699 * 8272236925540996054440172449761.
When is the next prime in the sequence?

Formalization: Does there exist a prime term after a(4)?
-/
theorem oeis_102847_conjecture_0 : ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  sorry
