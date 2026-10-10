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
# Determinant of odd composite sum indicator matrix

Determinant of the $n \times n$ $(0,1)$-matrix with $(i,j)$-entry ($1 \le i, j \le n$) equal to $1$
if and only if $i + j$ is $2$ or an odd composite number.

*References:*
- [A228591](https://oeis.org/A228591)
-/

namespace OeisA228591

open Matrix

/-- Determinant of the $n \times n$ $(0,1)$-matrix with $(i,j)$-entry ($1 \le i, j \le n$) equal
to $1$ if and only if $i + j$ is $2$ or an odd composite number. -/
def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let k := i.val + j.val + 2
    if k = 2 ∨ (k % 2 = 1 ∧ ¬ k.Prime) then 1 else 0
  M.det

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_7 : a 7 = -1 := by native_decide

/--
Conjecture: $a(n) = 0$ for no $n > 15$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 15) : a n ≠ 0 := by
  sorry

end OeisA228591
