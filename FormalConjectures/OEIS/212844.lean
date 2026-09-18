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
# Remainder of $2^{n+2}$ modulo $n$

The sequence $a(n) = 2^{n+2} \bmod n$.

*References:*
- [A212844](https://oeis.org/A212844)
-/

namespace OeisA212844

/-- $a(n) = 2^{n+2} \bmod n$. -/
def a (n : ℕ) : ℕ :=
  2 ^ (n + 2) % n

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by decide

/--
"Conjecture: every integer $k \ge 0$ appears in $a(n)$ at least once."
-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) : ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OeisA212844
