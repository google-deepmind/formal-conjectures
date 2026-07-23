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

open Rat

/--
A064169: Numerator - denominator in n-th harmonic number, $1 + 1/2 + 1/3 + \dots + 1/n$.
-/
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  -- The difference in ℤ is non-negative for n ≥ 1. Int.natAbs ensures the output is ℕ.
  Int.natAbs (hn.num - hn.den)


theorem a_one : A064169 1 = 0 := by
  simp_rw [A064169]
  norm_num[harmonic]

theorem a_two : A064169 2 = 1 := by
  ((norm_num[A064169]))

theorem a_three : A064169 3 = 5 := by
  norm_num [A064169]

theorem a_four : A064169 4 = 13 := by
  zify[A064169]
  norm_num[harmonic]


/-- Conjecture: for n > 2, n divides a(n-2) if and only if n is a prime. Checked up to 20000. -/
theorem oeis_64169_conjecture_0 (n : ℕ) (hn : n > 2) :
  (n ∣ A064169 (n - 2)) ↔ n.Prime :=
by sorry
