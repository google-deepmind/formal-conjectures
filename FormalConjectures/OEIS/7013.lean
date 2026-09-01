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
# Catalan-Mersenne numbers

Catalan-Mersenne numbers: $a(0) = 2$; for $n \ge 0$, $a(n+1) = 2^{a(n)} - 1$.

*References:*
- [A007013](https://oeis.org/A007013)
-/

namespace OeisA7013

/-- Catalan-Mersenne numbers: $a(0) = 2$, $a(n+1) = 2^{a(n)} - 1$. -/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 2
  | n + 1 => 2 ^ a n - 1

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 7 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 127 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 170141183460469231731687303715884105727 := by rfl

/--
Catalan-Mersenne conjecture: All terms of the Catalan-Mersenne sequence are prime.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : (a n).Prime := by
  sorry

end OeisA7013
