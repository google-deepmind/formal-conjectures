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

open Real

/--
A145355: $a(n) = \mathrm{round}(\mathrm{round}(\sqrt{n!})/|(\mathrm{round}(\sqrt{n!}))^2 - n!|)$.
The provided sequence starts at $n=2$. The definition works for $n=0, 1$ as well, provided we accept the behavior of $\mathbb{R}$ division by zero, which in Mathlib is typically $0$ but the result is not significant since the sequence is defined for $n \ge 2$ where the denominator is nonzero.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let fact_r : ℝ := Nat.cast (Nat.factorial n)
  let r_int : ℤ := round (sqrt fact_r)
  let r_real : ℝ := Int.cast r_int
  let den_val : ℝ := abs (r_real^2 - fact_r)
  (round (r_real / den_val)).toNat


theorem a_two : a 2 = 1 := by
  delta a
  norm_num [ ((Int.floor_eq_iff.mpr _) :_=(1:ℤ)),←not_lt, false,round_eq, Real.sqrt_lt',←lt_sub_iff_add_lt]

theorem a_three : a 3 = 1 := by
  delta a
  norm_num only[Nat.factorial,round_eq, ((Int.floor_eq_iff.2 _) :_=(2 :ℤ)),Int.toNat,←not_lt, true, abs_of_neg, ←lt_sub_iff_add_lt,Real.sqrt_lt, and_self_iff]

theorem a_four : a 4 = 5 := by
  delta a
  norm_num[Int.toNat,show round (sqrt 24) = 5 by {norm_num only [ ←not_lt, false,round_eq, true,Real.sqrt_lt',Int.floor_eq_iff, ←lt_sub_iff_add_lt, and_self]},round_eq, false,Nat.factorial]

theorem a_five : a 5 = 11 := by
  delta a
  norm_num [ ((Int.floor_eq_iff.2 _) :_=(11: Int)),round_eq,←not_lt,Int.toNat,←lt_sub_iff_add_lt,Real.sqrt_lt]


/--
oeis_145355_conjecture_0: This sequence suggests that the distance between a factorial and the closest power is tightly bounded.

Formalization: The sequence $a(n)$ is bounded.
This is the most direct mathematical interpretation of the data provided for $a(n)$.
-/
theorem oeis_145355_conjecture_0 : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → a n ≤ C := by
  sorry
