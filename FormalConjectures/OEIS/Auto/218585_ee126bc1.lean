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
A218585: Number of ways to write $n$ as $x+y$ with $0<x\le y$ and $x^2+xy+y^2$ prime.
-/
def A218585 (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).sum fun x ↦
    let y := n - x
    if Nat.Prime (x * x + x * y + y * y) then 1 else 0

-- Basic sequence values (keeping these as they were in the prompt)
theorem a_one : A218585 1 = 0 := by
  sorry

theorem a_two : A218585 2 = 1 := by
  sorry

theorem a_three : A218585 3 = 1 := by
  sorry

theorem a_four : A218585 4 = 1 := by
  sorry

/-- Conjecture: a(n)>0 for all n>1 with the only exception n=8. -/
theorem oeis_218585_conjecture_0 :
  (∀ n : ℕ, 1 < n → n ≠ 8 → A218585 n > 0) ∧ (A218585 8 = 0) := by
  sorry
