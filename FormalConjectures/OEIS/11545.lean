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
# A011545

a(n) is the integer whose decimal digits are the first n+1 decimal digits of π.

*References:*
- [A011545](https://oeis.org/A011545)
-/

namespace OeisA11545

open Real Int

/-- a n is the integer whose decimal digits are the first n+1 decimal digits of π. -/
noncomputable def a (n : ℕ) : ℕ :=
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by
  delta a
  norm_num[((Int.floor_eq_iff.mpr _) :⌊ π⌋ = ↑3),Int.toNat, false,le_of_lt Real.pi_gt_three,Real.pi_lt_four]

@[category test, AMS 11]
theorem a_1 : a 1 = 31 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.2 ⟨by linear_combination 10 * (.pi_gt_d20),by ·linear_combination 10 *.pi_lt_d20⟩):⌊_⌋ = 31)

@[category test, AMS 11]
theorem a_2 : a 2 = 314 := by
  simp_all[a]
  exact (congr_arg _) ((Int.floor_eq_iff.mpr ⟨by ·linear_combination 100 *.pi_gt_d20,by·linear_combination 100 *.pi_lt_d20⟩ ) ) |>.trans (Int.toNat_natCast _)

@[category test, AMS 11]
theorem a_3 : a 3 = 3141 := by
  symm
  norm_num[a]
  exact (.symm ((congr_arg _) ((Int.floor_eq_iff.2 ⟨by linear_combination 1000*.pi_gt_d20,by linear_combination 1000*.pi_lt_d20⟩):⌊_⌋=3141)))

/--
Wolfgang Haken (1977) conjectured that no term of this sequence is a perfect square, and estimated the probability that this conjecture is false to be smaller than 10^-9.
-/
@[category research open, AMS 11]
theorem conjecture1 : ∀ n, ¬ IsSquare (a n) := by
  sorry

/--
Number of collisions occurring in a system consisting of an infinitely massive, rigid wall at the origin, a ball with mass m stationary at position x1 > 0, and a ball with mass (10^2n)m at position x2 > x1 and rolling toward the origin, assuming perfectly elastic collisions and no friction.

Strictly speaking, this property, which is equivalent to the statement that the interval (m*Pi, Pi/arctan(1/m)) does not contain an integer for all m = 10^n, is not known to be true for sure. In other words, we do not know for certain that A332045 does not contain a power of 10.
-/
@[category research open, AMS 11]
theorem conjecture2 :
    ∀ n : ℕ, ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) :=
  by sorry

end OeisA11545
