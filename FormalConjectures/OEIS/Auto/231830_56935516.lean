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
A231830: $a(0) = 1$; for $n > 0$, $a(n) = 1 + 4 \cdot \prod_{i=1}^{n-1} a(i)^2$.
The recurrence relation for $n > 1$ is $a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1$.
-/
def a : ℕ → ℕ
| 0 => 1
| 1 => 5
| n + 2 => (a (n + 1) - 1) * (a (n + 1))^2 + 1


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 5 := by
  rfl

theorem a_two : a 2 = 101 := by
  rfl

theorem a_three : a 3 = 1020101 := by
  classical constructor


/--
OEIS A231830 conjecture: Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.
-/
theorem oeis_231830_conjecture_0 : ∀ n : ℕ, Squarefree (a n) := by
  sorry
