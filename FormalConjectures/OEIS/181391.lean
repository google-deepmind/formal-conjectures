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
# Van Eck's sequence (OEIS A181391)

Van Eck's sequence starts with zero. If the current value has occurred before, the next value is
the distance to its most recent earlier occurrence; otherwise the next value is zero.

*References:*
- [OEIS A181391](https://oeis.org/A181391)
- N. J. A. Sloane, [Some Open Problems](https://neilsloane.com/doc/EMMay2016.pdf#page=14)
-/

namespace OeisA181391

/-- The state used to generate Van Eck's sequence at a given index. The map `lastSeen` records
the most recent occurrence strictly before the current index. -/
structure State where
  current : ℕ
  lastSeen : ℕ → Option ℕ

/-- Advance the sequence from index `n`, recording the old current value only after computing the
next value. -/
def step (n : ℕ) (s : State) : State :=
  { current := match s.lastSeen s.current with
      | some j => n - j
      | none => 0
    lastSeen := Function.update s.lastSeen s.current (some n) }

/-- The state of Van Eck's sequence at index `n`. -/
def state : ℕ → State
  | 0 => ⟨0, fun _ ↦ none⟩
  | n + 1 => step n (state n)

/-- Van Eck's sequence, indexed from zero. -/
def a (n : ℕ) : ℕ :=
  (state n).current

/-- The public sequence satisfies the state transition used in its definition. -/
@[category API, AMS 11]
theorem a_succ (n : ℕ) :
    a (n + 1) = match (state n).lastSeen (a n) with
      | some j => n - j
      | none => 0 := by
  rfl

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_8 : a 8 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_9 : a 9 = 6 := by
  rfl

/-- [OEIS A181391](https://oeis.org/A181391) conjectures: "every number eventually appears." -/
@[category research open, AMS 11]
theorem conjecture : Function.Surjective a := by
  sorry

end OeisA181391
