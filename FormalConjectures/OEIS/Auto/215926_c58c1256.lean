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

open Nat Set

/--
A215926: Smallest deficient number $k$ such that the product $k \cdot n$ is non-deficient (perfect or abundant).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sigma1(m) is defined as m.divisors.sum id
  let sigma1 (m : ℕ) : ℕ := m.divisors.sum id
  -- We define the set of candidate k values and take its infimum (which is the minimum element).
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}


theorem a_two : a 2 = 3 := by
  delta a
  classical apply Nat.isLeast_find ⟨3,by decide⟩|>.csInf_eq

theorem a_three : a 3 = 2 := by
  delta and a
  focus apply Nat.isLeast_find ⟨2,by decide⟩ |>.csInf_eq

theorem a_four : a 4 = 3 := by
  delta a
  apply Nat.isLeast_find ⟨3,by decide⟩|>.csInf_eq

theorem a_five : a 5 = 4 := by
  delta a
  apply Nat.isLeast_find ⟨4,by decide⟩|>.csInf_eq

/--
Conjecture: a(n) is 1, 3, or a power of 2.
This is OEIS A215926 Conjecture 1.
Note: The sequence is listed for n >= 2.
-/
theorem oeis_215926_conjecture_0 (n : ℕ) (hn : 2 ≤ n) : a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by sorry
