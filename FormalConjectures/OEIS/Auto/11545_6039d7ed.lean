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

open Real Int

/--
A011545: $a(n)$ is the integer whose decimal digits are the first $n+1$ decimal digits of $\pi$.
This is equivalent to $a(n) = \lfloor \pi \cdot 10^n \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The calculation is $\lfloor \pi \cdot 10^n \rfloor$.
  -- We use Real.floor, which returns an Int, and convert it to a natural number.
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat


theorem a_zero : a 0 = 3 := by
  delta a
  norm_num[((Int.floor_eq_iff.mpr _) :⌊ π⌋ = ↑3),Int.toNat, false,le_of_lt Real.pi_gt_three,Real.pi_lt_four]

theorem a_one : a 1 = 31 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.2 ⟨by linear_combination 10 * (.pi_gt_d20),by ·linear_combination 10 *.pi_lt_d20⟩):⌊_⌋ = 31)

theorem a_two : a 2 = 314 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.mpr ⟨by ·linear_combination 100 *.pi_gt_d20,by·linear_combination 100 *.pi_lt_d20⟩ ) ) |>.trans (Int.toNat_natCast _)

theorem a_three : a 3 = 3141 := by
  symm
  norm_num[a]
  exact (.symm ((congr_arg _) ((Int.floor_eq_iff.2 ⟨by linear_combination 1000*.pi_gt_d20,by linear_combination 1000*.pi_lt_d20⟩):⌊_⌋=3141)))

/--
A property which is equivalent to the conjecture that the number of collisions
in the described physical system (with mass ratio $10^{2n}$) is $a(n)$:
the interval $(\pi \cdot 10^n, \pi / \arctan(1/10^n))$ does not contain an integer.
The mass ratio $m$ in the comment is interpreted as $\frac{M}{m}$ in the physics setup,
which is $10^{2n}$, so $\sqrt{m}=10^n$.

Note: The OEIS comment uses $m=10^n$ for the $R^2$ term where $R=10^n$ in the physics formula.
We formalize the statement $\forall n \in \mathbb{N}, \nexists k \in \mathbb{Z}$ such that
$\pi \cdot 10^n < k < \pi / \arctan(1/10^n)$.
-/
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) :=
  by sorry
