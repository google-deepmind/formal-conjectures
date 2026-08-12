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
# A GCD-Driven Sequence with Universal Jumps

OEIS A260194 begins with three ones and then adds the greatest common divisor of the current term
and the term two places earlier. The open question asks whether every positive integer occurs as
an adjacent difference.

*References:*
- [OEIS A260194](https://oeis.org/A260194)
-/

namespace OeisA260194

/-- Three consecutive values of A260194, carried as the state of its recursion. -/
structure State where
  first : ℕ
  second : ℕ
  third : ℕ

/-- Advance three consecutive terms by the recurrence
$a(n+1) = a(n) + \gcd(a(n),a(n-2))$. -/
def State.next (s : State) : State :=
  ⟨s.second, s.third, s.third + Nat.gcd s.third s.first⟩

/-- The state after `n` shifts, initialized by the three terms $1,1,1$. -/
def state : ℕ → State
  | 0 => ⟨1, 1, 1⟩
  | n + 1 => (state n).next

/-- OEIS A260194, shifted so that Lean index zero is the first OEIS term. -/
def a (n : ℕ) : ℕ :=
  (state n).first

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by rfl

@[category test, AMS 11]
theorem a_7 : a 7 = 9 := by rfl

@[category test, AMS 11]
theorem a_8 : a 8 = 10 := by rfl

@[category test, AMS 11]
theorem a_9 : a 9 = 12 := by rfl

/-- [OEIS A260194](https://oeis.org/A260194) asks:
"Does every positive integer occur as a difference in this sequence?" -/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ d > 0, ∃ n, a (n + 1) = a n + d := by
  sorry

end OeisA260194
