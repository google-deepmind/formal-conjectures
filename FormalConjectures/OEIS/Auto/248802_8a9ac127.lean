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

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac


theorem a_zero : a 0 = 11 := by
  dsimp [a]
  norm_num

theorem a_one : a 1 = 19 := by
  dsimp [a]
  norm_num

theorem a_two : a 2 = 67 := by
  dsimp [a]
  norm_num

theorem a_three : a 3 = 13 := by
  dsimp [a]
  norm_num

/--
Conjecture 5: a(138n+6) = 1669 for n >= 0 and n <> 2 mod 5.
-/
theorem oeis_248802_conjecture_5 (n : ℕ) (h : n % 5 ≠ 2) : a (138 * n + 6) = 1669 := by
  sorry
