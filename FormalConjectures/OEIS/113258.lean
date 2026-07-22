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
# Ascending descending base exponent transform of factorials

Ascending descending base exponent transform of factorials.

*References:*
- [A113258](https://oeis.org/A113258)
-/

namespace OeisA113258

/--
The primary defining sequence `a`.
a(n) is the ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 11 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 125 := by rfl

/--
Is there a nontrivial power after a(4) = 5^3?
-/
@[category research open, AMS 11]
theorem conjecture :
  answer(sorry) ↔ ∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e := by
  sorry

end OeisA113258
