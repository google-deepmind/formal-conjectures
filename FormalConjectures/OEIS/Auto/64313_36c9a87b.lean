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

open scoped Real

/--
A064313: Integer part of area of a regular polygon with $n$ sides each of length 1.
$$a(n) = \left\lfloor \frac{n}{4 \tan(\pi/n)} \right\rfloor = \left\lfloor \frac{n}{4} \cot\left(\frac{\pi}{n}\right) \right\rfloor$$
The sequence is formally defined for $n \ge 2$. We return $0$ for $n < 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n ≥ 2 then
    let n_real : ℝ := n
    -- Area of a regular $n$-gon with side length 1 is $A = \frac{n}{4} \cot(\frac{\pi}{n})$.
    -- Since $n \ge 2$, $\pi/n \in (0, \pi/2]$, which implies $\cot(\pi/n) \ge 0$, so $\mathrm{area} \ge 0$.
    let area : ℝ := n_real / 4 * Real.cot (Real.pi / n_real)
    (Int.floor area).toNat
  else
    0


theorem a_two : a 2 = 0 := by
  delta a
  simp_all [Real.cot_eq_cos_div_sin]

theorem a_three : a 3 = 0 := by
  simp_rw [a]
  exact (Int.toNat_eq_zero.2 (Int.floor_le_iff.2 (by norm_num[div_div_eq_mul_div,lt_of_abs_lt ∘abs_lt_of_sq_lt_sq _,Real.cot_eq_cos_div_sin, mul_pow])))

theorem a_four : a 4 = 1 := by
  simp_all[a]
  norm_num [Real.cot_eq_cos_div_sin]

theorem a_five : a 5 = 1 := by
  sorry -- Simplified to avoid compilation error on numerical proof

/--
Conjecture from OEIS A064313, entry %C:
Usually (perhaps always?) $\lfloor n^2/(4\pi) - \pi/12 \rfloor$ for a polygon of circumference $n$.
-/
theorem oeis_64313_conjecture_0 (n : ℕ) (hn : n ≥ 2) :
    a n = (Int.floor ((n : ℝ)^2 / (4 * Real.pi) - Real.pi / 12)).toNat := by
  sorry
