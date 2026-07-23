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

open Nat

/--
A231577: Number of ways to write $n = x + y$ ($x, y > 0$) with $2^x + y(y+1)/2$ prime.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    -- 1 ≤ x < n ensures $x$ and $y$ are positive.
    if Nat.Prime (2 ^ x + y * (y + 1) / 2) then 1 else 0


theorem a_one : a 1 = 0 := by
  simp [a]

theorem a_two : a 2 = 1 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry

theorem a_four : a 4 = 1 := by
  sorry


/-- Conjecture: a(n) > 0 for all n > 1. -/
theorem oeis_231577_conjecture_0 : ∀ (n : ℕ), 1 < n → 0 < a n := by
  sorry
