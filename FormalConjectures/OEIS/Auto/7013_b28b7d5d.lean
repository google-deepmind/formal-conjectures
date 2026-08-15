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
A007013 Catalan-Mersenne numbers: $a(0) = 2$; for $n \ge 0$, $a(n+1) = 2^{a(n)} - 1$.
-/
def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1


theorem a_zero : a 0 = 2 := by
  rfl

theorem a_one : a 1 = 3 := by
  rfl

theorem a_two : a 2 = 7 := by
  rfl

theorem a_three : a 3 = 127 := by
  rfl

/--
A007013 conjecture: All terms of the Catalan-Mersenne sequence are prime.
This is the most common interpretation of the OEIS comment:
"All terms shown are primes, the status of the next term is currently unknown."
-/
theorem oeis_7013_conjecture_0 : ∀ (n : ℕ), Nat.Prime (a n) := by
  sorry
