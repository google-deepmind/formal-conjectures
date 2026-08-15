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
open Function

/--
A212844: $a(n) = 2^{n+2} \bmod n$.
Since the OEIS sequence starts at $n=1$, the Lean function $a(n)$ returns the $(n+1)$-th term of the sequence.
The $(n+1)$-th term is calculated by substituting $n+1$ into $2^{n+2} \bmod n$.
-/
def a : ℕ → ℕ
| 0     => 0
| (n+1) => (2 ^ ((n + 1) + 2)) % (n + 1)


theorem a_one : a 1 = 0 := by
  rfl

theorem a_two : a 2 = 0 := by
  rfl

theorem a_three : a 3 = 2 := by
  rfl

theorem a_four : a 4 = 0 := by
  rfl

/-- A212844 Conjecture: every integer k >= 0 appears in a(n) at least once. -/
theorem oeis_212844_conjecture_0 : Surjective a := by
  sorry
