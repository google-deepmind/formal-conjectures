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
# Recurrence with bitwise XOR

The sequence is defined by $a(0) = 0$, $a(1) = 1$, and for $n \ge 0$,
$$a(n+2) = (a(n+1) \mathbin{\mathrm{XOR}} (n+2)) - a(n),$$
where $\mathrm{XOR}$ is the bitwise exclusive-or operator on integers.

*References:*
- [A182510](https://oeis.org/A182510)-/

namespace OeisA182510

/-- Defining recurrence for $a(n)$. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = -8 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = -2 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 0 := by rfl

/--
Conjecture: the sequence contains 8 zeros.-/
@[category research open, AMS 11]
theorem conjecture1 : Set.ncard {n : ℕ | a n = 0} = 8 := by
  sorry

/--
Conjecture: more positive terms than negative.-/
@[category research open, AMS 11]
theorem conjecture2 :
    ∃ d_pos d_neg : ℝ,
      ({n : ℕ | 0 < a n}).HasDensity d_pos ∧
      ({n : ℕ | a n < 0}).HasDensity d_neg ∧
      d_neg < d_pos := by
  sorry

end OeisA182510
