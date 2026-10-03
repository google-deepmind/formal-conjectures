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
# Ways to write $n = x + y$ with $2^x + y(y+1)/2$ prime

Number of ways to write $n = x + y$ ($x, y > 0$) with $2^x + y(y+1)/2$ prime.

*References:*
- [A231577](https://oeis.org/A231577)
-/

namespace OeisA231577

/-- Number of ways to write $n = x + y$ ($x, y > 0$) with $2^x + y(y+1)/2$ prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Ico 1 n,
    let y := n - x
    if (2 ^ x + y * (y + 1) / 2).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by rfl

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 1) : a n > 0 := by
  sorry

end OeisA231577
