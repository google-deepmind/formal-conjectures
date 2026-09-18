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
import FormalConjectures.OEIS.«69191»

/-!
# Square root of the absolute value of the determinant of the prime sum indicator matrix

Square root of the absolute value of $\det(M_n)$, where $M_n$ is the $n \times n$ matrix with
$(i,j)$-entry ($1 \le i, j \le n$) equal to $1$ if $i + j$ is prime, and $0$ otherwise.

*References:*
- [A228552](https://oeis.org/A228552)
-/

namespace OeisA228552

/-- Square root of the absolute value of the determinant of the $n \times n$ matrix with
$(i,j)$-entry ($1 \le i, j \le n$) equal to $1$ if $i + j$ is prime, and $0$ otherwise. -/
def a (n : ℕ) : ℕ :=
  (OeisA69191.a n).natAbs.sqrt

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

/--
We conjecture that $a(n) > 0$ for all $n > 15$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 15) : a n > 0 := by
  sorry

end OeisA228552
