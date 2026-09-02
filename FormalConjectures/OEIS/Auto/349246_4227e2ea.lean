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
A349246: Number of ways to write $n$ as $w^8 + x^4 + 2y^4 + 4z^4 + t(t+1)$, where $w, x, y, z$, and $t$ are nonnegative integers.
-/
def A349246 (n : ℕ) : ℕ :=
  let B := Finset.range (n + 1)
  Finset.sum B $ fun w =>
  Finset.sum B $ fun x =>
  Finset.sum B $ fun y =>
  Finset.sum B $ fun z =>
  Finset.sum B $ fun t =>
    if w^8 + x^4 + 2 * y^4 + 4 * z^4 + t * (t + 1) = n then 1 else 0


theorem a_zero : A349246 0 = 1 := by
  rfl

theorem a_one : A349246 1 = 2 := by
  sorry -- placeholder for the provided proof block

theorem a_two : A349246 2 = 3 := by
  rfl

theorem a_three : A349246 3 = 4 := by
  sorry -- placeholder for the provided proof block

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... -/
theorem oeis_349246_conjecture_0 (n : ℕ) : A349246 n > 0 := by
  sorry
