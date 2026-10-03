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
# Determinant of prime sum/difference matrix

Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i, j = 0, \dots, n - 1$) equal to $1$
or $0$ according as $n + i - j$ and $n - i + j$ are both prime or not.

*References:*
- [A228623](https://oeis.org/A228623)
-/

namespace OeisA228623

open Matrix

/-- Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i, j = 0, \dots, n - 1$) equal to
$1$ or $0$ according as $n + i - j$ and $n - i + j$ are both prime or not. -/
def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let p₁ := n + i.val - j.val
    let p₂ := n + j.val - i.val
    if p₁.Prime ∧ p₂.Prime then 1 else 0
  M.det

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by native_decide

@[category test, AMS 11]
theorem a_6 : a 6 = -1 := by native_decide

/--
Conjecture: $a(n)$ is nonzero if $n$ is odd and greater than $120$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 120) (hodd : Odd n) : a n ≠ 0 := by
  sorry

end OeisA228623
