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
# Determinant of square/cube sum matrix

Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i, j = 1, \dots, n$) equal to $1$ or
$0$ according as $i + j$ is a square or not.

*References:*
- [A228624](https://oeis.org/A228624)
-/

namespace OeisA228624

open Matrix

/-- Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i, j = 1, \dots, n$) equal to $1$
or $0$ according as $i + j$ is a square or not. -/
def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := i.val + j.val + 2
    if (Nat.sqrt sum_one_based) ^ 2 = sum_one_based then 1 else 0
  M.det

open Classical in
/-- Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i, j = 1, \dots, n$) equal to $1$
or $0$ according as $i + j$ is a perfect cube or not. -/
noncomputable def b (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := i.val + j.val + 2
    if ∃ m : ℕ, m ^ 3 = sum_one_based then 1 else 0
  M.det

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

/--
Conjecture: $a(n)$ is nonzero for any $n > 21$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 21) : a n ≠ 0 := by
  sorry

/--
Conjecture: Let $A(n)$ be the $n \times n$ determinant
with $(i,j)$-entry equal to $1$ or $0$ according as $i + j$ is a cube or not. Then $A(n)$ is
nonzero for any $n > 176$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 176) : b n ≠ 0 := by
  sorry

end OeisA228624
