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
# Number of $0$'s in the binary expansion of $n^2$

For $n \ge 0$, $a(n)$ is the number of $0$'s in the base-$2$ representation of $n^2$
(with $a(0) = 1$).

*References:*
- [A214560](https://oeis.org/A214560)
-/

namespace OeisA214560

/-- `a n` is the number of $0$'s in the binary expansion of $n^2$, with `a 0 = 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 2 (n ^ 2)).count 0

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

/--
Conjecture: For every $x \ge 0$, there is an $i$ such that $a(n) > x$
for all $n > i$.
-/
@[category research open, AMS 11]
theorem conjecture (x : ℕ) : ∃ i : ℕ, ∀ n > i, x < a n := by
  sorry

end OeisA214560
