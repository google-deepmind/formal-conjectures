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
# Riesel Problem

Riesel problem: let $k=2n-1$; then $a(n)$ is the smallest $m \ge 1$ such that
$k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists.

*References:*
- [A108129](https://oeis.org/A108129)
-/

namespace OeisA108129
variable {m n : ℕ}

open Nat

open Classical in
/-- The primary defining sequence `a`.
Riesel problem: let $k=2n-1$; then $a(n)$ is the smallest $m \ge 1$ such that
$k \cdot 2^m-1$ is prime, or $-1$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  -- Use classical choice to find the minimum, or return -1 if no such prime exists.
  else if h : ∃ m, m ≠ 0 ∧ ((2 * n - 1) * 2 ^ m - 1).Prime then
    Nat.find h
  else
    -1

@[category API, AMS 11]
lemma a_of_isLeast (hm : IsLeast {m | m ≠ 0 ∧ ((2 * n - 1) * 2 ^ m - 1).Prime} m) : a n = m := by
  rw [a, if_neg (by rintro rfl; simp at hm), dif_pos ⟨m, hm.1⟩, find_of_isLeast hm]

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := a_of_isLeast <| by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := a_of_isLeast <| by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := a_of_isLeast <| by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := a_of_isLeast <| by decide

/--
It is conjectured that the integer $k = 509203$ is the smallest Riesel number,
that is, the first $n$ such that $a(n) = -1$ is $254602$.
-/
@[category research open, AMS 11]
theorem conjecture :
    a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) := by
  sorry

end OeisA108129
